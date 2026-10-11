import JPAIGuidelinesMapping

/-!
# AISI-facing compositional assurance case — public consequences only

Copyright (c) 2026 AI Assurance, Inc. All rights reserved.
The repository's License notice applies. No patent license is granted.

This is an independent technical contribution for reviewing selected questions
raised by Japan AISI's argumentation-based conformity assessment and CCAS vision.
It is NOT an AISI specification, an implementation of CCAS, an endorsement,
a certification, or a proof of an operational system's overall safety.

Source context: README.md, section 2.1 and references S4 / S5.
The policy-to-mathematics correspondence is an explicitly stated interpretation;
Lean checks the mathematical consequences, not that interpretation.

DISCLOSURE BOUNDARY
* Import the existing public abstraction without modifying it or its Kernel.
* Add only theorems over its existing arbitrary types, relations and obligations.
* Do not define a concrete actor model, packet/receipt format, validation parser,
  checker, controller, approval-update/revocation method, or deployment sequence.
* Do not expand Examples.toy. Its existing nonvacuity result remains the only
  concrete existence witness and is not a multi-organization deployment example.

PROOF BOUNDARY
HandoffLaws / AdapterLaws are explicit hypotheses, not certifications of a hidden
implementation. A checked logical result must still be connected to actual inputs,
identity, permissions, events, storage, time, intervention and safe physical actions.
An executed record has past validation provenance; this does not establish that
all real-world events were supplied or that a validation algorithm is correct.

A successful check is sufficient for the public gate's positive branch when an
allow request is made and the gate is not stopped. Admission alone is NOT assumed
to imply a successful check: no checker-completeness premise is introduced.

Only a successful check of THIS file at the target commit establishes its build
status. The original file's earlier CI result is not evidence for this addition.
-/

set_option autoImplicit false

universe uE vE uC uB uU uA uS uI uV vV

open CategoryTheory
open JPAIGuidelinesMapping

namespace AISICompositionalAssuranceCase

variable {E : Type uE} [Category.{vE} E]
variable {C : Type uC} {B : Type uB} {U : Type uU} {A : Type uA}
variable {S : Type uS} {I : Type uI}
variable {v : Semantics E C B U A}

/-- C1: compose arbitrary finite semantic paths, retaining binding and support at
EVERY stage. The second path starts at the actual endpoint of the first. Neither
actor counts nor actor identities nor a concrete handoff representation are fixed. -/
theorem composed_paths_preserve_bound_support
    (v : Semantics E C B U A) (laws : HandoffLaws v)
    (c : C) (root : B) (first second : List B)
    (hFirst : ValueChain.Valid v c root first)
    (hSecond : ValueChain.Valid v c (ValueChain.endpoint root first) second)
    (hBound : v.bound c root) (use : U)
    (hUse : v.scope (ValueChain.endpoint root (first ++ second)) use) :
    ∀ b ∈ root :: (first ++ second), v.bound c b ∧ v.scope b use := by
  have hPath := ValueChain.valid_append v c root first second hFirst hSecond
  have hBindings := ValueChain.every_stage_is_bound v laws c root
    (first ++ second) hPath hBound
  have hScopes := ValueChain.use_supported_at_every_handoff v laws c root
    (first ++ second) hPath use hUse
  intro b hb
  refine ⟨hBindings b hb, ?_⟩
  rcases List.mem_cons.mp hb with hRoot | hPathMem
  · subst b
    exact hScopes.1
  · exact hScopes.2 b hPathMem

/-- C1/C3: actual execution in the reference model entails all-stage binding and
scope, under the existing local checker and handoff obligations. -/
theorem execution_requires_every_stage
    (M : Interface v S I) (laws : AdapterLaws M) (handoffLaws : HandoffLaws v)
    (s : State E C B U S) (a : Attempt B U)
    (hExecuted : (capture M s a).decision = .executed) :
    ∀ b ∈ a.root :: a.path,
      v.bound (M.context s.control) b ∧ v.scope b a.use := by
  have hAdmitted := (Safety.execution_is_locally_admitted M laws s a hExecuted).2.2
  have hBindings := ValueChain.every_stage_is_bound v handoffLaws
    (M.context s.control) a.root a.path hAdmitted.chain hAdmitted.binding
  have hScopes := Safety.execution_respects_all_scopes M laws handoffLaws s a hExecuted
  intro b hb
  refine ⟨hBindings b hb, ?_⟩
  rcases List.mem_cons.mp hb with hRoot | hPathMem
  · subst b
    exact hScopes.1
  · exact hScopes.2.1 b hPathMem

/-- C3: a known binding or scope failure at any observed stage blocks execution.
A missing implementation proof is NOT itself a runtime observation of failure. -/
theorem unsupported_stage_cannot_execute
    (M : Interface v S I) (laws : AdapterLaws M) (handoffLaws : HandoffLaws v)
    (s : State E C B U S) (a : Attempt B U) (b : B)
    (hStage : b ∈ a.root :: a.path)
    (hFailure : ¬ v.bound (M.context s.control) b ∨ ¬ v.scope b a.use) :
    (capture M s a).decision ≠ .executed := by
  intro hExecuted
  have hStageSupport := execution_requires_every_stage M laws handoffLaws
    s a hExecuted b hStage
  rcases hFailure with hBinding | hScope
  · exact hBinding hStageSupport.1
  · exact hScope hStageSupport.2

/-- C3: failure of the already-public admission postcondition prevents execution.
This is a consequence of check_sound, not disclosure of a concrete checker. -/
theorem inadmissible_attempt_cannot_execute
    (M : Interface v S I) (laws : AdapterLaws M)
    (s : State E C B U S) (a : Attempt B U)
    (hFailure : ¬ Admission M s.control a) :
    (capture M s a).decision ≠ .executed := by
  intro hExecuted
  exact hFailure (Safety.execution_is_locally_admitted M laws s a hExecuted).2.2

/-- C6: the public gate admits its positive branch under the stated conditions.
No claim that every semantically admissible request passes a particular checker,
or that such a request exists in an arbitrary deployment, follows from this. -/
theorem successful_check_permits_execution
    (M : Interface v S I) (s : State E C B U S) (a : Attempt B U)
    (hRunning : s.halted = false) (hAllow : a.request = .allow)
    (hCheck : M.check s.control a = true) :
    (capture M s a).decision = .executed := by
  simp [capture, gate, hRunning, hAllow, hCheck]

/-- C4: changing context and changing its label back does not restore permission
without revalidation. No new revocation or receipt-freshness method is specified. -/
theorem profile_round_trip_cannot_reauthorize
    (M : Interface v S I) (laws : AdapterLaws M)
    (s : State E C B U S) (other : C) (a : Attempt B U) :
    (capture M (History.run M s
      [.reprofile other, .reprofile (M.context s.control)]) a).decision ≠ .executed := by
  exact History.profile_ABA_requires_revalidation M laws s other a

/-- C4: a validation attempt accepting no basis cannot create execution permission.
The actual validation predicate and its implementation remain abstract. -/
theorem failed_revalidation_cannot_execute
    (M : Interface v S I) (laws : AdapterLaws M)
    (s : State E C B U S) (input : I)
    (hRejected : ∀ b, ¬ M.validates s.control input b) (a : Attempt B U) :
    (capture M { s with control := M.revalidate s.control input } a).decision ≠
      .executed := by
  exact Safety.failed_revalidation_closes_gate M laws s input hRejected a

/-- C3: an explicit withhold request is never treated as execution. -/
theorem withhold_cannot_execute
    (M : Interface v S I) (s : State E C B U S) (a : Attempt B U)
    (hWithhold : a.request = .withhold) :
    (capture M s a).decision ≠ .executed := by
  exact Safety.withhold_never_executes M s a hWithhold

/-- C3: logical stop persists throughout an arbitrary finite command continuation.
This is not a claim about a physical emergency stop or an unmodeled reset path. -/
theorem stop_persists_through_history
    (M : Interface v S I) (commands : List (History.Command C B U I))
    (s : State E C B U S) (hStopped : s.halted = true) :
    (History.run M s commands).halted = true := by
  exact History.stopped_run_stays_stopped M commands s hStopped

/-- C2: expose both the existing assurance conclusion and an accepted validation
occurrence INSIDE the prefix preceding this record's capture. The witness comes
from the run and the existing local obligations, not from a certificate supplied
with every input. No concrete state, packet or workflow is serialized here. -/
theorem executed_record_has_prior_validation
    (M : Interface v S I) (laws : AdapterLaws M) (handoffLaws : HandoffLaws v)
    (s : S) (hInitial : ∀ b, ¬ M.available s b)
    (commands : List (History.Command C B U I))
    {V : Type uV} [Category.{vV} V] (publish : E ⥤ V) (r : Record E C B U)
    (hMem : r ∈ (History.run M (initial s) commands).history)
    (hExecuted : r.decision = .executed)
    (hExport : ResponsibilityOS.PreservesPolicy publish r.policyAt) :
    ExecutionAssurance M (initial s) commands publish r ∧
      ∃ (before after : List (History.Command C B U I)) (a : Attempt B U)
        (earlier middle : List (History.Command C B U I)) (input : I),
        commands = before ++ History.Command.attempt a :: after ∧
        r = capture M (History.run M (initial s) before) a ∧
        before = earlier ++ History.Command.revalidate input :: middle ∧
        M.validates (History.run M (initial s) earlier).control input a.root ∧
        Admission M (History.run M (initial s) before).control a := by
  have hAssurance := execution_has_prior_assurance M laws handoffLaws s hInitial
    commands publish r hMem hExecuted hExport
  obtain ⟨before, after, a, hSplit, hCapture, hOrigin, hAdmission⟩ :=
    hAssurance.priorValidation
  obtain ⟨earlier, middle, input, hValidationSplit, hValidated⟩ :=
    History.origin_is_validation_occurrence M before a.root (initial s) hOrigin
  exact ⟨hAssurance, ⟨before, after, a, earlier, middle, input,
    hSplit, hCapture, hValidationSplit, hValidated, hAdmission⟩⟩

/-- C0/C5/C6: a single review entry point joins the existing finite-history theorem,
fail-closed admission, and the conditional positive branch of the public gate.

HistoryAssurance retains all of the original theorem's conclusions: equality to
the no-pruning reference history, historical execution assurance, historical policy
preservation, the exhaustive/disjoint monitoring partition, occurrence counts and
current-support checks. None is replaced by a Boolean certificate or assumed as
an input. All original hypotheses, including historical-policy preservation and
in-range pruning, remain explicit. The additional branches are existing public
consequences, not a new operational approval algorithm or checker completeness.
-/
theorem compositional_assurance_case [DecidableEq C]
    (M : Interface v S I) (laws : AdapterLaws M) (handoffLaws : HandoffLaws v)
    (s : S) (hInitial : ∀ b, ¬ M.available s b)
    (commands : List (History.Command C B U I)) (now : Nat)
    (hTime : History.CutoffsWithin now commands)
    (plan : Governance.MonitoringPlan E C B U)
    {V : Type uV} [Category.{vV} V] (publish : E ⥤ V)
    (hExport : ∀ r ∈ Accountability.pruneExpired now
      (History.run M (initial s) commands).history,
      r.decision = .executed → ResponsibilityOS.PreservesPolicy publish r.policyAt) :
    HistoryAssurance M s commands now plan publish ∧
      (∀ (st : State E C B U S) (a : Attempt B U),
        ¬ Admission M st.control a → (capture M st a).decision ≠ .executed) ∧
      (∀ (st : State E C B U S) (a : Attempt B U),
        st.halted = false → a.request = .allow → M.check st.control a = true →
          (capture M st a).decision = .executed) := by
  refine ⟨no_silent_responsibility_gap M laws handoffLaws s hInitial
    commands now hTime plan publish hExport, ?_, ?_⟩
  · intro st a hFailure
    exact inadmissible_attempt_cannot_execute M laws st a hFailure
  · intro st a hRunning hAllow hCheck
    exact successful_check_permits_execution M st a hRunning hAllow hCheck

end AISICompositionalAssuranceCase
