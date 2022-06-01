import stormpy

from .property import Property, OptimalityProperty, Specification
from .holes import Hole, Holes, DesignSpace

import os
import re
import uuid

import logging
logger = logging.getLogger(__name__)

class PrismParser:

    @classmethod
    def read_prism_sketch(cls, sketch_path, constant_str):
        '''
        Read PRISM program from sketch_path; parse hole definitions (if any);
        parse constant definitions and substitute these into the PRISM program.
        '''

        # parse the program
        prism, hole_definitions = PrismParser.load_sketch_prism(sketch_path)
        expression_parser = stormpy.storage.ExpressionParser(prism.expression_manager)
        expression_parser.set_identifier_mapping(dict())
        logger.debug("PRISM model type: " + str(prism.model_type))

        # parse constants
        constant_map = None
        if constant_str != '':
            logger.info(f"Assuming constant definitions: '{constant_str}' ...")
            constant_map = PrismParser.map_constants(prism, expression_parser, constant_str)
            prism = prism.define_constants(constant_map)
            prism = prism.substitute_constants()

        # parse hole definitions
        hole_expressions = None
        design_space = None
        if len(hole_definitions) > 0:
            logger.info("Processing hole definitions ...")
            prism, hole_expressions, design_space = PrismParser.parse_holes(
                prism, expression_parser, hole_definitions)
        
        # success
        return prism, hole_expressions, design_space, constant_map

        


    @classmethod
    def load_sketch_prism(cls, sketch_path):
        # read lines
        with open(sketch_path) as f:
            sketch_lines = f.readlines()

        # replace hole definitions with constants
        hole_re = re.compile(r'^hole\s+(.*?)\s+(.*?)\s+in\s+\{(.*?)\};$')
        sketch_output = []
        hole_definitions = {}
        for line in sketch_lines:
            match = hole_re.search(line)
            if match is not None:
                hole_type = match.group(1)
                hole_name = match.group(2)
                hole_options = match.group(3).replace(" ", "")
                hole_definitions[hole_name] = hole_options
                line = f"const {hole_type} {hole_name};"
            sketch_output.append(line)

        # store modified sketch to a temporary file
        tmp_path = sketch_path + str(uuid.uuid4())
        with open(tmp_path, 'w') as f:
            for line in sketch_output:
                print(line, end="", file=f)

        # try to parse temporary sketch and then delete it
        try:
            prism = stormpy.parse_prism_program(tmp_path, prism_compat=True)
            os.remove(tmp_path)
        except:
            os.remove(tmp_path)
            exit(1)

        return prism, hole_definitions

 
    @classmethod
    def map_constants(cls, prism, expression_parser, constant_str):
        constant_str = constant_str.replace(" ", "")
        if constant_str == "":
            return dict()
        
        constant_map = dict()
        constant_definitions = constant_str.split(",")
        prism_constants = {c.name:c for c in prism.constants}

        for constant_definition in constant_definitions:
            key_value = constant_definition.split("=")
            if len(key_value) != 2:
                raise ValueError(f"Expected key=value pair, got '{constant_definition}'.")

            expr = expression_parser.parse(key_value[1])
            name = key_value[0]
            constant = prism_constants[name].expression_variable
            constant_map[constant] = expr
        return constant_map


    @classmethod
    def parse_holes(cls, prism, expression_parser, hole_definitions):

        # parse hole definitions
        holes = Holes()
        hole_expressions = []
        for hole_name,definition in hole_definitions.items():
            options = definition.split(",")
            expressions = [expression_parser.parse(o) for o in options]
            hole_expressions.append(expressions)

            options = list(range(len(expressions)))
            option_labels = [str(e) for e in expressions]
            hole = Hole(hole_name, options, option_labels)
            holes.append(hole)

        # check that all undefined constants are indeed the holes
        undefined_constants = [c for c in prism.constants if not c.defined]
        assert len(undefined_constants) == len(holes), "some constants were unspecified"

        # convert single-valued holes to a defined constant
        trivial_holes_definitions = {}
        nontrivial_holes = Holes()
        nontrivial_hole_expressions = []
        for hole_index,hole in enumerate(holes):
            if hole.size == 1:
                trivial_holes_definitions[prism.get_constant(hole.name).expression_variable] = hole_expressions[hole_index][0]
            else:
                nontrivial_holes.append(hole)
                nontrivial_hole_expressions.append(hole_expressions[hole_index])
        holes = nontrivial_holes
        hole_expressions = nontrivial_hole_expressions

        # substitute trivial holes
        prism = prism.define_constants(trivial_holes_definitions)
        prism = prism.substitute_constants()
    
        design_space = DesignSpace(holes)

        return prism, hole_expressions, design_space

 
    @classmethod
    def parse_specification(cls, properties_path, prism = None, constant_map = None):

        logger.info(f"Loading properties from {properties_path} ...")

        # read lines
        lines = []
        with open(properties_path) as file:
            for line in file:
                # line = line.replace(" ", "")
                line = line.replace("\n", "")
                if not line or line == "" or line.startswith("//"):
                    continue
                lines.append(line)

        # strip relative error
        lines_properties = ""
        relative_error_re = re.compile(r'^(.*)\{(.*?)\}(=\?.*?$)')
        relative_error_str = None
        for line in lines:
            match = relative_error_re.search(line)
            if match is not None:
                relative_error_str = match.group(2)
                line = match.group(1) + match.group(3)
            lines_properties += line + ";"
        optimality_epsilon = float(relative_error_str) if relative_error_str is not None else 0

        # parse all properties
        properties = []
        optimality_property = None

        if prism is not None:
            props = stormpy.parse_properties_for_prism_program(lines_properties, prism)
        else:
            props = stormpy.parse_properties_without_context(lines_properties)
        for prop in props:
            rf = prop.raw_formula
            assert rf.has_bound != rf.has_optimality_type, "optimizing formula contains a bound or a comparison formula does not"
            if rf.has_bound:
                # comparison formula
                properties.append(prop)
            else:
                # optimality formula
                assert optimality_property is None, "two optimality formulae specified"
                optimality_property = prop

        if constant_map is not None:
            # substitute constants in properties
            for p in properties:
                p.raw_formula.substitute(constant_map)
            if optimality_property is not None:
                optimality_property.raw_formula.substitute(constant_map)

        # wrap properties
        properties = [Property(p) for p in properties]
        if optimality_property is not None:
            optimality_property = OptimalityProperty(optimality_property, optimality_epsilon)

        specification = Specification(properties,optimality_property)
        return specification




    

    
    