import stormpy
from .statistic import Statistic
from .models import MarkovChain, DTMC, MDP

from .quotient import QuotientContainer
from .quotient_pomdp import POMDPQuotientContainer

from .synthesizer import SynthesizerAR, SynthesizerHybrid

from ..profiler import Timer,Profiler

from ..sketch.holes import Holes,DesignSpace

import math
from collections import defaultdict

import logging
logger = logging.getLogger(__name__)


class HoleTree:

    def __init__(self, options):
        self.nodes = [options]

    def __str__(self):
        return ",".join([str(x) for x in self.nodes])

    def split(self, mem, inconsistent_options):

        old_options = self.nodes[mem]
        
        # create child holes
        children = []
        for option in inconsistent_options:
            child_options = old_options.copy()
            child_options.remove(option)
            children.append(child_options)

        # store child nodes
        self.nodes[mem] = children[0]
        new_indices = []
        for child in children[1:]:
            new_indices.append(len(self.nodes))
            self.nodes.append(child)

        return new_indices

    def update_memory_updates(self, mem, new_indices):
        for index,options in enumerate(self.nodes):
            if mem in options:
                options.extend(new_indices)



class SynthesizerPOMDP:

    def __init__(self, sketch, method):
        assert sketch.is_pomdp
        self.sketch = sketch
        self.synthesizer = None
        if method == "ar":
            self.synthesizer = SynthesizerAR
        elif method == "hybrid":
            self.synthesizer = SynthesizerHybrid
        self.total_iters = 0
        Profiler.initialize()

    def print_stats(self):
        pass
    
    def synthesize(self, family, print_stats = True):
        self.sketch.quotient.discarded = 0
        synthesizer = self.synthesizer(self.sketch)
        family.property_indices = self.sketch.design_space.property_indices
        assignment = synthesizer.synthesize(family)
        if print_stats:
            synthesizer.print_stats()
        print(assignment)
        self.total_iters += synthesizer.stat.iterations_mdp
        return assignment


    def strategy_full(self):
        self.sketch.quotient.pomdp_manager.set_memory_size(Sketch.pomdp_memory_size)
        self.sketch.quotient.unfold_memory()
        self.synthesize(self.sketch.design_space)

    
    def strategy_iterative(self):
        mem_size = POMDPQuotientContainer.initial_memory_size
        # while True:
        for x in range(2):
            POMDPQuotientContainer.current_family_index = mem_size
            logger.info("Synthesizing optimal k={} controller ...".format(mem_size) )
            self.sketch.quotient.set_global_memory_size(mem_size)
            self.synthesize(self.sketch.design_space)
            mem_size += 1

    
    def solve_mdp(self, family):

        # solve quotient MDP
        self.sketch.quotient.build(family)
        mdp = family.mdp
        spec = mdp.check_specification(self.sketch.specification)

        # hole scores = sum of scores wrt individual formulae
        hole_scores = {}
        all_results = spec.constraints_result.results.copy()
        if spec.optimality_result is not None:
            all_results.append(spec.optimality_result)
        # print([res.primary_scores for res in all_results])
        for index,res in enumerate(all_results):
            for hole,score in res.primary_scores.items():
                hole_score = hole_scores.get(hole,0)
                hole_scores[hole] = hole_score + score

        result = spec.optimality_result
        selection = result.primary_selection
        
        # print()
        # print()
        # # print(dir())
        # print(mdp.states)
        # scheduler = result.primary.result.scheduler
        # print(self.sketch.quotient.coloring.state_to_holes)
        # print(spec.optimality_result.primary_scores)
        # p = spec.optimality_result.primary.result
        # for state in range(mdp.states):
        #     print(state)
        #     local_choice = scheduler.get_choice(state).get_deterministic_choice()
        #     global_choice = mdp.model.get_choice_index(state,local_choice)
        #     row = mdp.model.transition_matrix.get_row(global_choice)
        #     print("scheduler choice: {}/{}".format(local_choice,global_choice))
        #     quotient_choice = mdp.quotient_choice_map[global_choice]
        #     print("choice colors: ", self.sketch.quotient.coloring.action_to_hole_options[quotient_choice])
        #     print("matrix row: ", row)
        #     quotient_state = mdp.quotient_state_map[state]
        #     relevant_holes = self.sketch.quotient.coloring.state_to_holes[quotient_state]
        #     obs = None
        #     for hole in relevant_holes:
        #         for obs in range(self.sketch.quotient.observations):
        #             action_holes = self.sketch.quotient.observation_action_holes[obs]
        #             if hole in action_holes:
        #                 selected_obs = obs
        #                 selected_mem = action_holes.index(hole)
        #                 hole_is_action = True
        #                 break
        #             memory_holes = self.sketch.quotient.observation_memory_holes[obs]
        #             if hole in memory_holes:
        #                 selected_obs = obs
        #                 selected_mem = memory_holes.index(hole)
        #                 hole_is_action = False
        #                 break
        #         print("hole corresponds to observation ({},{}) [{}]".format(selected_obs,selected_mem,hole_is_action))
        #     # print("relevant holes: ", self.sketch.quotient.)
        #     print(p.get_values()[state])
        #     print()
        #     # print(prototype_state)
        # print()
        # print()
        
        
        choice_values = result.primary_choice_values
        expected_visits = result.primary_expected_visits
        # scores = result.primary_scores
        scores = hole_scores

        return mdp, spec, selection, choice_values, expected_visits, scores

    
    def strategy_expected(self):

        # assuming optimality
        assert self.sketch.specification.optimality is not None

        num_obs = self.sketch.quotient.observations
        observation_successors = self.sketch.quotient.pomdp_manager.observation_successors

        # for each observation, create a root of an action hole tree
        action_hole_trees = [None] * num_obs
        memory_hole_trees = [None] * num_obs
        for obs in range(num_obs):
            ah = self.sketch.quotient.action_hole_prototypes[obs]
            if ah is not None:
                action_hole_trees[obs] = HoleTree(ah.options)
            memory_hole_trees[obs] = HoleTree([0])

        # start with k=1
        best_assignment = None
        fsc_synthesis_timer = Timer()
        fsc_synthesis_timer.start()

        # while True:
        for iteration in range(3):

            print("\n------------------------------------------------------------\n")

            print([str(tree) for tree in action_hole_trees])
            print([str(tree) for tree in memory_hole_trees])
            
            # construct and solve the quotient
            family = self.sketch.design_space
            mdp,spec,selection,choice_values,expected_visits,hole_scores = self.solve_mdp(family)
            
            # check whether that primary direction was not enough ?
            if not spec.optimality_result.can_improve:
                logger.info("Optimum matches the upper bound of a symmetry-free MDP.")
                break
            
            # synthesize optimal assignment
            synthesized_assignment = self.synthesize(family)

            # print status
            opt = "-"
            if self.sketch.specification.optimality.optimum is not None:
                opt = round(self.sketch.specification.optimality.optimum,3)
            elapsed = round(fsc_synthesis_timer.read(),1)
            memory_injections = sum(self.sketch.quotient.observation_memory_size) - num_obs
            logger.info("FSC synthesis: elapsed {} s, opt = {}, injections: {}.".format(elapsed, opt, memory_injections))
            logger.info("FSC: {}".format(best_assignment))
           
            # identify hole that we want to improve
            selected_hole = None
            selected_options = None
            if synthesized_assignment is not None:
                # remember the solution
                best_assignment = synthesized_assignment

                # synthesized solution exists: hole of interest is the one where
                # the fully-observable improves upon the synthesized action
                # the most

                # # for each state of the sub-MDP, compute potential state improvement
                # state_improvement = [None] * mdp.states
                # scheduler = spec.optimality_result.primary.result.scheduler
                # for state in range(mdp.states):
                #     # nothing to do if the state is not labeled by any hole
                #     quotient_state = mdp.quotient_state_map[state]
                #     holes = self.sketch.quotient.coloring.state_to_holes[quotient_state]
                #     if not holes:
                #         continue
                #     hole = list(holes)[0]
                    
                #     # get choice obtained by the MDP model checker
                #     choice_0 = mdp.model.transition_matrix.get_row_group_start(state)
                #     mdp_choice = scheduler.get_choice(state).get_deterministic_choice()
                #     mdp_choice = choice_0 + mdp_choice
                    
                #     # get choice implied by the synthesizer
                #     syn_option = synthesized_assignment[hole].options[0]
                #     nci = mdp.model.nondeterministic_choice_indices
                #     for choice in range(nci[state],nci[state+1]):
                #         choice_global = mdp.quotient_choice_map[choice]
                #         choice_color = self.sketch.quotient.coloring.action_to_hole_options[choice_global]
                #         if choice_color == {hole:syn_option}:
                #             syn_choice = choice
                #             break
                    
                #     # estimate improvement
                #     mdp_value = choice_values[mdp_choice]
                #     syn_value = choice_values[syn_choice]
                #     improvement = abs(syn_value - mdp_value)
                    
                #     state_improvement[state] = improvement

                # # had there been no new assignment, the hole of interest will
                # # be the one with the maximum score in the symmetry-free MDP

                # # map improvements in states of this sub-MDP to states of the quotient
                # quotient_state_improvement = [None] * self.sketch.quotient.quotient_mdp.nr_states
                # for state in range(mdp.states):
                #     quotient_state_improvement[mdp.quotient_state_map[state]] = state_improvement[state]

                # # extract DTMC corresponding to the synthesized solution
                # dtmc = self.sketch.quotient.build_chain(synthesized_assignment)

                # # compute expected visits for this dtmc
                # dtmc_visits = stormpy.synthesis.compute_expected_number_of_visits(MarkovChain.environment, dtmc.model).get_values()
                # dtmc_visits = list(dtmc_visits)

                # # handle infinity- and zero-visits
                # if self.sketch.specification.optimality.minimizing:
                #     dtmc_visits = QuotientContainer.make_vector_defined(dtmc_visits)
                # else:
                #     dtmc_visits = [ value if value != math.inf else 0 for value in dtmc_visits]

                # # weight state improvements with expected visits
                # # aggregate these weighted improvements by holes
                # hole_differences = [0] * family.num_holes
                # hole_states_affected = [0] * family.num_holes
                # for state in range(dtmc.states):
                #     quotient_state = dtmc.quotient_state_map[state]
                #     improvement = quotient_state_improvement[quotient_state]
                #     if improvement is None:
                #         continue

                #     weighted_improvement = improvement * dtmc_visits[state]
                #     assert not math.isnan(weighted_improvement), "{}*{} = nan".format(improvement,dtmc_visits[state])
                #     hole = list(self.sketch.quotient.coloring.state_to_holes[quotient_state])[0]
                #     hole_differences[hole] += weighted_improvement
                #     hole_states_affected[hole] += 1

                # hole_differences_avg = [0] * family.num_holes
                # for hole in family.hole_indices:
                #     if hole_states_affected[hole] != 0:
                #         hole_differences_avg[hole] = hole_differences[hole] / hole_states_affected[hole]
                # all_scores = {hole:hole_differences_avg[hole] for hole in family.hole_indices}
                # nonzero_scores = {h:v for h,v in all_scores.items() if v>0}
                # if len(nonzero_scores) > 0:
                #     hole_scores = nonzero_scores
                # else:
                #     hole_scores = all_scores

            max_score = max(hole_scores.values())
            if max_score > 0:
                hole_scores = {h:v for h,v in hole_scores.items() if v / max_score > 0.01 }
            with_max_score = [hole for hole in hole_scores if hole_scores[hole] == max_score]
            selected_hole = with_max_score[0]
            # selected_hole = holes_to_inject[0]
            selected_options = selection[selected_hole]

            # identify observation having this hole
            for obs in range(self.sketch.quotient.observations):
                action_holes = self.sketch.quotient.observation_action_holes[obs]
                if selected_hole in action_holes:
                    selected_obs = obs
                    selected_mem = action_holes.index(selected_hole)
                    hole_is_action = True
                    break
                memory_holes = self.sketch.quotient.observation_memory_holes[obs]
                if selected_hole in memory_holes:
                    selected_obs = obs
                    selected_mem = memory_holes.index(selected_hole)
                    hole_is_action = False
                    break


            print()
            hole_scores_printable = {self.sketch.design_space[hole].name : score for hole,score in hole_scores.items()} 
            print("hole scores: ", hole_scores)
            print("hole scores (printable): ", hole_scores_printable)
            print("selected hole: {}, ({})".format(selected_hole, family[selected_hole]))
            print("hole corresponds to observation ({},{}) [{}]".format(selected_obs,selected_mem,hole_is_action))
            print("hole is inconsistent in options: ", selected_options)
            assert len(selected_options) > 1
            
            # split hole option and break symmetry
            if hole_is_action:
                new_indices = action_hole_trees[selected_obs].split(selected_mem,selected_options)
            else:
                assert None
                new_indices = memory_hole_trees[selected_obs].split(selected_mem,selected_options)
            print("new indices: ", new_indices)

            
            # increase memory size in the selected observation to reflect all inconsistencies
            # detect which observation were affected by this increase
            old_successor_size = self.sketch.quotient.pomdp_manager.max_successor_memory_size
            for x in range(len(selected_options)-1):
                self.sketch.quotient.increase_memory_size(selected_obs)
            new_successor_size = self.sketch.quotient.pomdp_manager.max_successor_memory_size
            affected_obs = []

            for obs in range(num_obs):
                if new_successor_size[obs] > old_successor_size[obs]:
                    affected_obs.append(obs)
            print("observations affected by injection: ", affected_obs)

            # update memory nodes
            for obs in affected_obs:
                memory_hole_trees[obs].update_memory_updates(selected_mem,new_indices)

            print([str(tree) for tree in action_hole_trees])
            print([str(tree) for tree in memory_hole_trees])
            
            # inject memory
            
            print()
            logger.info(">>>Injected memory into observation {}.".format(selected_obs))

            # reconstruct design space using the history of symmetry breakings
            
            restricted_family = self.sketch.design_space.copy()
            for obs in range(num_obs):

                action_holes = self.sketch.quotient.observation_action_holes[obs]
                if len(action_holes) > 0:
                    tree = action_hole_trees[obs]
                    for index,options in enumerate(tree.nodes):
                        restricted_family[action_holes[index]].assume_options(options)

                memory_holes = self.sketch.quotient.observation_memory_holes[obs]
                if len(memory_holes) > 0:
                    tree = memory_hole_trees[obs]
                    for index,options in enumerate(tree.nodes):
                        restricted_family[memory_holes[index]].assume_options(options)

            print(restricted_family)
            logger.debug("Symmetry breaking: reduced design space from {} to {}".format(self.sketch.design_space.size, restricted_family.size))
            self.sketch.design_space = restricted_family
                


    def run(self):
        # self.strategy_full()
        self.strategy_iterative()
        # self.strategy_expected()




