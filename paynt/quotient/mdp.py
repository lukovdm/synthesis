import paynt.quotient.quotient

import stormpy
import payntbind

import logging
logger = logging.getLogger(__name__)


class Variable:

    def __init__(self, variable, model):
        assert variable.has_boolean_type() or variable.has_integer_type(), \
            f"variable {variable.name} is neither integer nor boolean"
        self.variable = variable

        assert model.has_state_valuations(), "model has no state valuations"
        if self.has_integer_type:
            value_getter = model.state_valuations.get_integer_value
        else:
            value_getter = model.state_valuations.get_boolean_value
        domain = set()
        for state in range(model.nr_states):
            value = value_getter(state,self.variable)
            domain.add(value)
        domain = list(domain)
        # conversion of boolean variables to integers
        if self.has_boolean_type:
            domain = [1 if value else 0 for value in domain]
        domain = sorted(domain)
        self.domain = domain


    @property
    def name(self):
        return self.variable.name

    @property
    def has_integer_type(self):
        return self.variable.has_integer_type()

    @property
    def has_boolean_type(self):
        return self.variable.has_boolean_type()

    @property
    def domain_min(self):
        return self.domain[0]

    @property
    def domain_max(self):
        return self.domain[-1]

    @property
    def hole_domain(self):
        '''
        Hole domain does not include the maximum value.
        '''
        return self.domain[:-1]

    def __str__(self):
        # domain = "bool" if self.has_boolean_type else f"[{self.domain_min}..{self.domain_max}]"
        domain = f"[{self.domain_min}..{self.domain_max}]"
        return f"{self.name}:{domain}"

    @classmethod
    def from_model(cls, model, program_variables):
        variables = [Variable(v,model) for v in program_variables]
        variables = [v for v in variables if len(v.domain) > 1]
        return variables



class DecisionTreeNode:

    def __init__(self, parent):
        self.parent = parent
        self.is_terminal = True
        self.variable_index = None
        self.hole = None

    @property
    def child_nodes(self):
        return [] if self.is_terminal else [self.child_true,self.child_false]

    @property
    def is_true_child(self):
        return self is self.parent.child_true

    def set_variable(self, variable_index:int):
        '''
        Associate (an index of) a variable with the node.
        '''
        assert self.is_terminal, "redefining existing variable for a tree node"
        self.is_terminal = False
        self.variable_index = variable_index
        self.child_false = DecisionTreeNode(self)
        self.child_true = DecisionTreeNode(self)

    def set_variable_by_name(self, variable_name:str, decision_tree):
        name_to_variable_index = {var.name:index for index,var in enumerate(decision_tree.variables)}
        variable_index = name_to_variable_index[variable_name]
        self.set_variable(variable_index)

    def create_hole(self, family, action_labels, variables):
        '''
        Create a unique hole associated with this node. Terminal nodes are associated with actions selection, where
        additional "don't care" action is added.
        '''
        # create a unique hole index based on the current number of holes
        self.hole = family.num_holes
        if self.is_terminal:
            prefix = "A"
            option_labels = action_labels #+ ["__dont_care__"]
        else:
            var = variables[self.variable_index]
            prefix = variables[self.variable_index].name
            option_labels = variables[self.variable_index].hole_domain
        hole_name = f"{prefix}_{self.hole}"
        family.add_hole(hole_name, option_labels)


    def collect_bounds(self):
        lower_bounds = []
        upper_bounds = []
        node = self
        while node.parent is not None:
            if node.is_true_child:
                bounds = upper_bounds
            else:
                bounds = lower_bounds
            bounds.append(node.parent.hole)
            node = node.parent
        return lower_bounds,upper_bounds



class DecisionTree:

    def __init__(self, model, program_variables):

        self.model = model
        self.variables = Variable.from_model(model,program_variables)
        logger.debug(f"found the following variables: {[str(v) for v in self.variables]}")
        self.num_nodes = 0
        self.root = DecisionTreeNode(None)

    def build_coloring(self):
        coloring = None
        return coloring

    def collect_nodes(self, node_condition=None):
        node_queue = [self.root]
        output_nodes = []
        while node_queue:
            node = node_queue.pop(0)
            if node_condition is None or node_condition(node):
                output_nodes.append(node)
            node_queue += node.child_nodes
        return output_nodes

    def collect_terminals(self):
        node_condition = lambda node : node.is_terminal
        return self.collect_nodes(node_condition)

    def collect_nonterminals(self):
        node_condition = lambda node : not node.is_terminal
        return self.collect_nodes(node_condition)

    def create_family(self, action_labels):
        family = paynt.family.family.Family()
        for node in self.collect_nodes():
            node.create_hole(family, action_labels, self.variables)
        return family


def custom_decision_tree(mdp, program_variables):
    dt = DecisionTree(mdp, program_variables)

    decide = lambda node,var_name : node.set_variable_by_name(var_name,dt)

    decide(dt.root,"clk")
    main = dt.root.child_false

    decide(dt.root.child_false, "y")
    decide(dt.root.child_false.child_true, "x")
    decide(dt.root.child_false.child_true.child_true, "x")

    # decide(main,"y")
    # decide(main.child_false,"x")
    # decide(main.child_true,"x")
    # decide(main.child_true.child_true,"x")

    # decide(main, "y")
    # decide(main.child_false, "x")
    # decide(main.child_false.child_true, "x")
    # decide(main.child_true, "x")
    # decide(main.child_true.child_true, "x")
    return dt



class MdpQuotient(paynt.quotient.quotient.Quotient):

    def __init__(self, mdp, specification):
        super().__init__(specification=specification)

        # get variables before choice origins are lost
        assert mdp.has_choice_origins(), "model has no choice origins"
        program_variables = mdp.choice_origins.program.variables

        target_states = self.identify_target_states(mdp,self.get_property())
        mdp = payntbind.synthesis.restoreActionsInTargetStates(mdp,target_states)
        self.quotient_mdp = mdp
        self.choice_destinations = payntbind.synthesis.computeChoiceDestinations(self.quotient_mdp)
        self.action_labels,self.choice_to_action = payntbind.synthesis.extractActionLabels(mdp)

        decision_tree = custom_decision_tree(mdp, program_variables)
        family = decision_tree.create_family(self.action_labels)
        print("family = ", family)

        hole_bounds = [None for hole in range(family.num_holes)]
        for node in decision_tree.collect_nodes():
            hole_bounds[node.hole] = node.collect_bounds()
        # print("hole bounds = ", hole_bounds)

        hole_variable = [len(decision_tree.variables) for _ in range(family.num_holes)]
        hole_domain = [[] for h in range(family.num_holes)]
        for node in decision_tree.collect_nonterminals():
            hole_variable[node.hole] = node.variable_index
            hole_domain[node.hole] = family.hole_to_option_labels[node.hole]
        # print("hole variables = ", hole_variable)
        # print("hole domain = ", hole_domain)
        stormpy_variables = [v.variable for v in decision_tree.variables]

        self.decision_tree = decision_tree
        self.hole_variable = hole_variable
        self.is_action_hole = [var == len(self.decision_tree.variables) for var in self.hole_variable]
        self.coloring = payntbind.synthesis.ColoringSmt(
            mdp.nondeterministic_choice_indices, self.choice_to_action,
            mdp.state_valuations, stormpy_variables,
            hole_variable, hole_bounds,
            family.family, hole_domain
        )
        self.design_space = paynt.family.family.DesignSpace(family)


    def build_unsat_result(self):
        constraints_result = paynt.verification.property_result.ConstraintsResult([])
        optimality_result = paynt.verification.property_result.MdpOptimalityResult(None)
        optimality_result.can_improve = False
        analysis_result = paynt.verification.property_result.MdpSpecificationResult(constraints_result,optimality_result)
        return analysis_result

    def build(self, family):
        # family.parent_info = None
        if family.parent_info is None:
            choices = self.coloring.selectCompatibleChoices(family.family)
        else:
            choices = self.coloring.selectCompatibleChoices(family.family, family.parent_info.selected_choices)
        if choices.number_of_set_bits() == 0:
            family.mdp = None
            family.analysis_result = self.build_unsat_result()
            return

        # proceed as before
        family.selected_choices = choices
        family.mdp = self.build_from_choice_mask(choices)
        # assert family.mdp.model.nr_choices == self.quotient_mdp.nr_choices
        family.mdp.design_space = family


    def areChoicesConsistent(self, choices, mdp):
        return self.coloring.areChoicesConsistent(choices, mdp.design_space.family)

    def scheduler_is_consistent(self, mdp, prop, result):
        ''' Get hole options involved in the scheduler selection. '''

        scheduler = result.scheduler
        assert scheduler.memoryless and scheduler.deterministic
        state_to_choice = self.scheduler_to_state_to_choice(mdp, scheduler)
        choices = self.state_to_choice_to_choices(state_to_choice)
        consistent,hole_selection = self.areChoicesConsistent(choices, mdp)
        if mdp.is_deterministic:
            assert consistent, "obtained a DTMC, but the scheduler is not consistent"

        # convert selection to actual hole options
        for hole,values in enumerate(hole_selection):
            if self.is_action_hole[hole]:
                continue
            hole_selection[hole] = [self.design_space.hole_to_option_labels[hole].index(value) for value in values]
        for hole,options in enumerate(hole_selection):
            for option in options:
                assert option in mdp.design_space.hole_options(hole), f"option {option} is not in the family"

        return hole_selection, consistent


    def scheduler_get_quantitative_values(self, mdp, prop, result, selection):
        '''
        :return choice values
        :return expected visits
        :return hole scores
        '''

        inconsistent_assignments = {hole:options for hole,options in enumerate(selection) if len(options) > 0 }
        inconsistent_action_holes = [(hole,options) for hole,options in inconsistent_assignments.items() if self.is_action_hole[hole]]
        inconsistent_variable_holes = [(hole,options) for hole,options in inconsistent_assignments.items() if not self.is_action_hole[hole]]

        # choose splitter and force its score
        splitter = None

        # try action holes first
        for hole,options in inconsistent_action_holes:
            if len(options) > 1:
                splitter = hole
                break
        else:
            for hole,values in inconsistent_variable_holes:
                # pick an arbitrary value and find the corresponding hole option
                value = values[0]
                for option in mdp.design_space.hole_options(hole):
                    if mdp.design_space.hole_to_option_labels[hole][option] == value:
                        splitter = hole
                        selection[splitter] = [option]
                        # TODO make sure this selection will split this hole in half
                        break
                else:
                    assert False, "this should not occur..."
        assert splitter is not None, "inconsistent action hole with exactly 1 option?"

        inconsistent_differences = {splitter:10}
        return None, None, inconsistent_differences

    def split(self, family, incomplete_search):

        mdp = family.mdp
        assert not mdp.is_deterministic

        # split family wrt last undecided result
        result = family.analysis_result.undecided_result()
        hole_assignments = result.primary_selection
        scores = result.primary_scores

        splitters = self.holes_with_max_score(scores)
        splitter = splitters[0]
        if self.is_action_hole[splitter]:
            assert len(hole_assignments[splitter]) > 1
            core_suboptions,other_suboptions = self.suboptions_enumerate(mdp, splitter, hole_assignments[splitter])
        else:
            assert len(hole_assignments[splitter]) == 1
            splitter_option = hole_assignments[splitter][0]
            index = family.hole_options(splitter).index(splitter_option)
            options = mdp.design_space.hole_options(splitter)
            core_suboptions = [options[:index], options[index:]]
            other_suboptions = []

        new_design_space, suboptions = self.discard(mdp, hole_assignments, core_suboptions, other_suboptions, incomplete_search)

        # construct corresponding design subspaces
        design_subspaces = []
        family.splitter = splitter
        parent_info = family.collect_parent_info(self.specification)
        for suboption in suboptions:
            subholes = new_design_space.subholes(splitter, suboption)
            design_subspace = paynt.family.family.DesignSpace(subholes, parent_info)
            design_subspace.hole_set_options(splitter, suboption)
            design_subspaces.append(design_subspace)

        return design_subspaces
