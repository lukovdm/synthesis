import paynt.quotient.posmg
import paynt.synthesizer.synthesizer
import paynt.quotient.pomdp
import paynt.verification.property_result
import paynt.models.models

import stormpy

import logging
logger = logging.getLogger(__name__)

class SynthesizerAR(paynt.synthesizer.synthesizer.Synthesizer):

    @property
    def method_name(self):
        return "AR"

    def check_specification(self, family):
        ''' Check specification for mdp or smg based on self.quotient '''
        mdp = family.mdp

        if isinstance(self.quotient, paynt.quotient.posmg.PosmgQuotient):
            model = self.quotient.create_smg_from_mdp(mdp)
        else:
            model = mdp

        # check constraints
        admissible_assignment = None
        spec = self.quotient.specification
        if family.constraint_indices is None:
            family.constraint_indices = spec.all_constraint_indices()
        results = [None for _ in spec.constraints]
        for index in family.constraint_indices:
            constraint = spec.constraints[index]
            result = paynt.verification.property_result.MdpPropertyResult(constraint)
            results[index] = result

            # check primary direction
            result.primary = model.model_check_property(constraint)
            if result.primary.sat is False:
                result.sat = False
                break

            # check if the primary scheduler is consistent
            result.primary_selection,consistent = self.quotient.scheduler_is_consistent(mdp, constraint, result.primary.result)
            if consistent:
                assignment = family.assume_options_copy(result.primary_selection)
                if constraint.is_conditional and result.primary.result.has_scheduler: # support for conditional properties
                    chain = model.model.apply_scheduler(result.primary.result.scheduler.get_memoryless_scheduler_for_memory_state(0))
                    dtmc = paynt.models.models.Mdp(chain)
                else:
                    dtmc = self.quotient.build_assignment(assignment)
                res = dtmc.check_specification(self.quotient.specification)
                # assert result.primary.value == res.constraints_result.results[index].value, f"Inconsistent results for constraint {index}: {result.primary.value} vs {res.constraints_result.results[index].value}"
                # accepting_dtmc returns (is_accepting, value); index [0] for the
                # boolean. Without it the non-empty tuple is always truthy, so a
                # member that does NOT satisfy the constraint would be wrongly
                # accepted and returned as the admissible assignment.
                member_accepting = res.accepting_dtmc(self.quotient.specification)[0]
                # For conditional properties a member only genuinely satisfies the
                # constraint if its condition is reachable: otherwise P[A|B] is
                # 0/0 = inf, which Storm reports as satisfying any P>x bound.
                if member_accepting and constraint.is_conditional:
                    condition_operator = stormpy.logic.ProbabilityOperator(
                        constraint.formula.subformula.conditional_subformula
                    )
                    condition_value = stormpy.model_checking(
                        dtmc.model, condition_operator
                    ).at(dtmc.model.initial_states[0])
                    member_accepting = condition_value > 0
                if member_accepting:
                    result.sat = True
                    admissible_assignment = assignment

            # primary direction is SAT: check secondary direction to see whether all SAT
            result.secondary = model.model_check_property(constraint, alt=True)
            if mdp.is_deterministic and result.primary.value != result.secondary.value:
                logger.warning("WARNING: model is deterministic but min<max")
            # The secondary (worst-case) bound claims that *every* member of the
            # family satisfies the constraint. For a conditional property this
            # bound is unsound: a member whose condition is unreachable has an
            # undefined conditional probability (P[A|B] with P[B]=0), which Storm
            # evaluates as inf and therefore reports as satisfying any P>x bound.
            # Such a family must not be accepted via the shortcut (which would
            # return an arbitrary, possibly condition-unreachable member); instead
            # leave it undecided so it is refined down to verified members.
            if result.secondary.sat and not constraint.is_conditional:
                result.sat = True
                continue

        spec_result = paynt.verification.property_result.MdpSpecificationResult()
        spec_result.constraints_result = paynt.verification.property_result.ConstraintsResult(results)

        # check optimality
        if spec.has_optimality and not spec_result.constraints_result.sat is False:
            opt = spec.optimality
            result = paynt.verification.property_result.MdpOptimalityResult(opt)

            # check primary direction
            result.primary = model.model_check_property(opt)
            if not result.primary.improves_optimum:
                # OPT <= LB
                result.can_improve = False
            else:
                # LB < OPT, check if LB is tight
                result.primary_selection,consistent = self.quotient.scheduler_is_consistent(mdp, opt, result.primary.result)
                result.can_improve = True
                if consistent:
                    # LB < OPT and it's tight, double-check the constraints and the value on the DTMC
                    result.can_improve = False
                    assignment = family.assume_options_copy(result.primary_selection)
                    if opt.is_conditional and result.primary.result.has_scheduler: # support for conditional properties
                        chain = model.model.apply_scheduler(result.primary.result.scheduler.get_memoryless_scheduler_for_memory_state(0))
                        dtmc = paynt.models.models.Mdp(chain)
                    else:
                        dtmc = self.quotient.build_assignment(assignment)
                    res = dtmc.check_specification(self.quotient.specification)
                    if res.constraints_result.sat and spec.optimality.improves_optimum(res.optimality_result.value):
                        result.improving_assignment = assignment
                        result.improving_value = res.optimality_result.value
            spec_result.optimality_result = result

        spec_result.evaluate(family, admissible_assignment)
        family.analysis_result = spec_result

    def verify_family(self, family):
        self.quotient.build(family)

        # TODO include iteration_game in iteration? is it necessary?
        if isinstance(self.quotient, paynt.quotient.posmg.PosmgQuotient):
            self.stat.iteration_game(family.mdp.states)
        else:
            self.stat.iteration(family.mdp)

        if self.quotient.specification.contains_conditional_properties():
            # unfold conditional properties
            if not self.quotient.is_condition_reachable(family.mdp.model):
                spec_result = paynt.verification.property_result.MdpSpecificationResult()
                spec_result.can_improve = False
                spec_result.improving_assignment = None
                family.analysis_result = spec_result
                return

        self.check_specification(family)

    def update_optimum(self, family):
        ia = family.analysis_result.improving_assignment
        if ia is None:
            return
        if not self.quotient.specification.has_optimality:
            self.best_assignment = ia
            return
        iv = family.analysis_result.improving_value
        if not self.quotient.specification.optimality.improves_optimum(iv):
            return
        self.quotient.specification.optimality.update_optimum(iv)
        self.best_assignment = ia
        self.best_assignment_value = iv
        # logger.info(f"value {round(iv,4)} achieved after {round(paynt.utils.timer.GlobalTimer.read(),2)} seconds")
        if isinstance(self.quotient, paynt.quotient.pomdp.PomdpQuotient):
            self.stat.new_fsc_found(family.analysis_result.improving_value, ia, self.quotient.policy_size(ia))

    def synthesize_one(self, family):
        families = [family]
        while families:
            if self.resource_limit_reached():
                break
            family = families.pop(-1)
            self.verify_family(family)
            self.update_optimum(family)
            if not self.quotient.specification.has_optimality and self.best_assignment is not None:
                break
            # break
            if family.analysis_result.can_improve is False:
                self.explore(family)
                continue
            # undecided
            subfamilies = self.quotient.split(family)
            families = families + subfamilies
        return self.best_assignment
