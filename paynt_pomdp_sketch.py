# using PAYNT for POMDP sketches

import paynt.cli
import paynt.parser.sketch

import paynt.quotient.pomdp_family

import os
import random

def load_sketch(project_path):
    project_path = os.path.abspath(project_path)
    sketch_path = os.path.join(project_path, "sketch.templ")
    properties_path = os.path.join(project_path, "sketch.props")    
    pomdp_sketch = paynt.parser.sketch.Sketch.load_sketch(sketch_path, properties_path)
    return pomdp_sketch


def investigate_hole_assignment(pomdp_sketch, hole_assignment):
    print("investigating hole assignment: ", hole_assignment)
    pomdp = pomdp_sketch.build_pomdp(hole_assignment)

    # return a random k-FSC
    num_nodes = 2
    fsc = paynt.quotient.pomdp_family.FSC(num_nodes, pomdp.nr_observations)
    random.seed(42)
    for node in range(num_nodes):
        for obs in range(pomdp.nr_observations):
            available_actions = pomdp_sketch.observation_to_choice_label_indices[obs]
            fsc.action_function[node][obs] = random.choice(available_actions)
            fsc.update_function[node][obs] = random.randrange(num_nodes)
    return fsc

def investigate_fsc(pomdp_sketch, fsc):
    print(f"investigating FSC with {fsc.num_nodes} nodes")
    dtmc_sketch = pomdp_sketch.build_dtmc_sketch(fsc)
    assert dtmc_sketch is not None
    exit()

# enable PAYNT logging
paynt.cli.setup_logger()

# load sketch
project_path="models/pomdp/sketches/obstacles"
pomdp_sketch = load_sketch(project_path)
print("specification: ", pomdp_sketch.specification)
print("design space:\n", pomdp_sketch.design_space)
print("number of holes: ", pomdp_sketch.design_space.num_holes)
print("design space size: {} members".format(pomdp_sketch.design_space.size))

# fix some hole options
hole_options = [[hole.options[0]] for hole in pomdp_sketch.design_space]
hole_assignment = pomdp_sketch.design_space.assume_options_copy(hole_options)

# investigate this hole assignment and return an FSC
fsc = investigate_hole_assignment(pomdp_sketch, hole_assignment)

# investigate this FSC and return a hole assignment for which this FSC is violating
violating_hole_assignment = investigate_fsc(pomdp_sketch, fsc)
print("violating hole_assignment: " violating_hole_assignment)
