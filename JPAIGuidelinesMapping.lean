import ResponsibilityOS

/-!
# Responsibility OS × AI事業者ガイドライン — public abstraction

This file publishes semantic interfaces, local proof obligations and compositional
assurance theorems. It does NOT publish a packet format, a receipt parser, a private
controller, a validation algorithm, or an approval-revocation implementation.
The imported Responsibility OS Kernel is unchanged.

`C`, `B`, `U`, `A`, `S` and `I` are arbitrary types: contexts, assurance observations,
uses, actors, hidden controller states and hidden validation inputs. No fields of
these types are specified here. A list of `B` is a mathematical path of observations,
not a serialization or a specification of receipt contents.

There are two distinct proof boundaries:
* `HandoffLaws` and `AdapterLaws` are explicit, LOCAL obligations for an adapter.
  They are not global axioms and are not proved for an undisclosed implementation.
* The reference gate, finite-path consequences, prior-validation provenance,
  exact retained-history equality and monitoring partition are proved below.
  No premise assumes that all output records already satisfy the headline theorem.

This public model deliberately does not claim verification of the removed private
checks. It does not use `opaque` to conceal source code that is still distributed.
Formal/operational correspondence, identity and input authenticity, suitable risk
policies, complete event capture, clocks, storage and physical safe stopping remain
external. Handoff is evidence continuity, not transfer of legal liability.

The mapping baseline and source-review status are in README.md. This is not a
certificate of compliance, safety or non-infringement. Build status must be established
for this exact source and its fixed dependencies; no successful build is asserted here.
-/

universe uE vE uC uB uU uA uS uI uV vV uW vW uO vO uF vF

open CategoryTheory

namespace JPAIGuidelinesMapping

attribute [local instance] ResponsibilityOS.IndexedAssurance.fiberCategory

/-- The public evidence view already used by the EU profile; no evidence payload format. -/
structure Evidence (E : Type uE) [Category.{vE} E] where
  source : E
  target : E
  trace : source ⟶ target

/-- Observations and relations, NOT concrete fields of a private assurance packet. -/
structure Semantics (E : Type uE) [Category.{vE} E]
    (C : Type uC) (B : Type uB) (U : Type uU) (A : Type uA) where
  evidence : B → Evidence E
  owner : B → A
  scope : B → U → Prop
  bound : C → B → Prop
  handoff : C → B → B → Prop

variable {E : Type uE} [Category.{vE} E]
variable {C : Type uC} {B : Type uB} {U : Type uU} {A : Type uA}
variable {S : Type uS} {I : Type uI}

/-- Local semantic obligations. Binding includes the application's justified
interpretation of evidence/document applicability; the interpretation is external. -/
structure HandoffLaws (v : Semantics E C B U A) : Prop where
  binding : ∀ c b d, v.handoff c b d → v.bound c b → v.bound c d
  scope : ∀ c b d, v.handoff c b d → ∀ u, v.scope d u → v.scope b u

namespace ValueChain

/-- A finite path of semantic handoff relations, not a concrete handoff checker. -/
def Valid (v : Semantics E C B U A) (c : C) (b : B) : List B → Prop
  | [] => True
  | d :: ds => v.handoff c b d ∧ Valid v c d ds

def endpoint (b : B) : List B → B
  | [] => b
  | d :: ds => endpoint d ds

/-- Local narrowing implies end-to-end narrowing over any finite path. -/
theorem no_scope_expansion (v : Semantics E C B U A) (laws : HandoffLaws v)
    (c : C) (b : B) (path : List B) (h : Valid v c b path) :
    ∀ u, v.scope (endpoint b path) u → v.scope b u := by
  induction path generalizing b with
  | nil => intro u hu; exact hu
  | cons d ds ih =>
      intro u hu
      exact laws.scope c b d h.1 u (ih d h.2 u hu)

/-- The actually used action is supported at the root and every intermediate stage. -/
theorem use_supported_at_every_handoff (v : Semantics E C B U A)
    (laws : HandoffLaws v) (c : C) (b : B) (path : List B)
    (h : Valid v c b path) (u : U) (hu : v.scope (endpoint b path) u) :
    v.scope b u ∧ ∀ d ∈ path, v.scope d u := by
  induction path generalizing b with
  | nil => exact ⟨hu, by simp⟩
  | cons d ds ih =>
      have ht := ih d h.2 hu
      refine ⟨laws.scope c b d h.1 u ht.1, ?_⟩
      intro x hx
      rcases List.mem_cons.mp hx with heq | hmem
      · subst x; exact ht.1
      · exact ht.2 x hmem

/-- Evidence/document binding survives the whole semantic path under local binding laws. -/
theorem every_stage_is_bound (v : Semantics E C B U A) (laws : HandoffLaws v)
    (c : C) (b : B) (path : List B) (h : Valid v c b path) (hb : v.bound c b) :
    ∀ d ∈ b :: path, v.bound c d := by
  induction path generalizing b with
  | nil =>
      intro d hd
      have heq := List.mem_singleton.mp hd
      subst d
      exact hb
  | cons d ds ih =>
      have hd := laws.binding c b d h.1 hb
      intro x hx
      rcases List.mem_cons.mp hx with heq | hmem
      · subst x; exact hb
      · exact ih d h.2 hd x hmem

/-- Concatenation preserves semantic continuity; it does not reconstruct omitted receipts. -/
theorem valid_append (v : Semantics E C B U A) (c : C) (b : B)
    (first second : List B) (hFirst : Valid v c b first)
    (hSecond : Valid v c (endpoint b first) second) :
    Valid v c b (first ++ second) := by
  induction first generalizing b with
  | nil => exact hSecond
  | cons d ds ih => exact ⟨hFirst.1, ih d hFirst.2 hSecond⟩

/-- Even an expansion unrelated to the currently requested use violates the local
handoff contract. A later narrowing does not justify that expanding step. -/
theorem scope_widening_is_not_handoff (v : Semantics E C B U A) (laws : HandoffLaws v)
    (c : C) (b d : B) (u : U) (hNew : v.scope d u) (hOld : ¬ v.scope b u) :
    ¬ v.handoff c b d := by
  intro h
  exact hOld (laws.scope c b d h u hNew)

end ValueChain

inductive Request where
  | allow | withhold | stop
  deriving DecidableEq, Repr

inductive Decision where
  | executed | held | stopped
  deriving DecidableEq, Repr

/-- Same public stop-dominant logical gate as the EU reference profile. -/
def gate (halted ready : Bool) (request : Request) : Decision :=
  match halted, request with
  | true, _ => .stopped
  | false, .stop => .stopped
  | false, .withhold => .held
  | false, .allow => if ready then .executed else .held

def Decision.isStopped : Decision → Bool
  | .stopped => true
  | _ => false

/-- A semantic event supplied to the reference runner. `root` and `path` are abstract
observations, not private approval/receipt data. Times are externally justified ticks. -/
structure Attempt (B : Type uB) (U : Type uU) where
  root : B
  path : List B
  use : U
  request : Request
  at : Nat
  retainUntil : Nat
  validWindow : at ≤ retainUntil

/-- Adapter signatures only. `S` and `I` have no public representation here.
`current` covers the application's justified freshness/reuse conditions.
The observation `route` includes the root actor; repeated/internal actors are allowed. -/
structure Interface (v : Semantics E C B U A) (S : Type uS) (I : Type uI) where
  context : S → C
  policy : S → ResponsibilityOS.ObservationPolicy E
  route : S → List A
  permitted : S → U → Prop
  available : S → B → Prop
  current : S → B → Prop
  revalidate : S → I → S
  reprofile : S → C → S
  validates : S → I → B → Prop
  check : S → Attempt B U → Bool

variable {v : Semantics E C B U A}

/-- A PUBLIC semantic postcondition, not the internal formula of an admission checker. -/
structure Admission (M : Interface v S I) (s : S) (a : Attempt B U) : Prop where
  available : M.available s a.root
  current : M.current s a.root
  binding : v.bound (M.context s) a.root
  chain : ValueChain.Valid v (M.context s) a.root a.path
  terminalUse : v.scope (ValueChain.endpoint a.root a.path) a.use
  configuredUse : M.permitted s a.use
  exactRoute : (a.root :: a.path).map v.owner = M.route s

/-- These are explicit adapter proof obligations, not implementations or global axioms.
An adapter is not certified merely by importing this file. In particular, `check_sound`
must be proved against the actual checker; metadata assertions alone are insufficient. -/
structure AdapterLaws (M : Interface v S I) : Prop where
  check_sound : ∀ s a, M.check s a = true → Admission M s a
  revalidate_origin : ∀ s i b,
    M.available (M.revalidate s i) b → M.validates s i b
  reprofile_closes : ∀ s c b, ¬ M.available (M.reprofile s c) b
  reprofile_context : ∀ s c, M.context (M.reprofile s c) = c

/-- Public observations retained for reasoning; no hidden-state or private payload snapshot. -/
structure Record (E : Type uE) [Category.{vE} E]
    (C : Type uC) (B : Type uB) (U : Type uU) where
  attempt : Attempt B U
  contextAt : C
  policyAt : ResponsibilityOS.ObservationPolicy E
  ready : Bool
  haltedBefore : Bool
  decision : Decision

structure State (E : Type uE) [Category.{vE} E]
    (C : Type uC) (B : Type uB) (U : Type uU) (S : Type uS) where
  control : S
  halted : Bool
  history : List (Record E C B U)

def initial (s : S) : State E C B U S := ⟨s, false, []⟩

def capture (M : Interface v S I) (s : State E C B U S)
    (a : Attempt B U) : Record E C B U :=
  ⟨a, M.context s.control, M.policy s.control, M.check s.control a, s.halted,
    gate s.halted (M.check s.control a) a.request⟩

/-- Public reference recording, not a private production transition or durable store. -/
def advance (M : Interface v S I) (s : State E C B U S)
    (a : Attempt B U) : State E C B U S :=
  let r := capture M s a
  ⟨s.control, r.decision.isStopped, r :: s.history⟩

namespace Safety

theorem execution_requires_permission (halted ready : Bool) (request : Request)
    (h : gate halted ready request = .executed) :
    halted = false ∧ request = .allow ∧ ready = true := by
  cases halted <;> cases ready <;> cases request <;> simp_all [gate]

/-- Gate-to-semantics connection, CONDITIONAL on the declared checker-soundness obligation. -/
theorem execution_is_locally_admitted (M : Interface v S I) (laws : AdapterLaws M)
    (s : State E C B U S) (a : Attempt B U)
    (h : (capture M s a).decision = .executed) :
    s.halted = false ∧ a.request = .allow ∧ Admission M s.control a := by
  have hp := execution_requires_permission s.halted (M.check s.control a) a.request h
  exact ⟨hp.1, hp.2.1, laws.check_sound s.control a hp.2.2⟩

theorem withhold_never_executes (M : Interface v S I) (s : State E C B U S)
    (a : Attempt B U) (h : a.request = .withhold) :
    (capture M s a).decision ≠ .executed := by
  cases hh : s.halted <;> simp [capture, gate, hh, h]

theorem stop_always_halts (M : Interface v S I) (s : State E C B U S)
    (a : Attempt B U) (h : a.request = .stop) : (advance M s a).halted = true := by
  cases hh : s.halted <;> simp [advance, capture, gate, Decision.isStopped, hh, h]

theorem stopped_state_remains_stopped (M : Interface v S I) (s : State E C B U S)
    (a : Attempt B U) (h : s.halted = true) : (advance M s a).halted = true := by
  simp [advance, capture, gate, Decision.isStopped, h]

theorem execution_respects_all_scopes (M : Interface v S I)
    (laws : AdapterLaws M) (handoffLaws : HandoffLaws v)
    (s : State E C B U S) (a : Attempt B U)
    (h : (capture M s a).decision = .executed) :
    v.scope a.root a.use ∧ (∀ b ∈ a.path, v.scope b a.use) ∧
      M.permitted s.control a.use := by
  have ha := (execution_is_locally_admitted M laws s a h).2.2
  have hs := ValueChain.use_supported_at_every_handoff v handoffLaws
    (M.context s.control) a.root a.path ha.chain a.use ha.terminalUse
  exact ⟨hs.1, hs.2, ha.configuredUse⟩

theorem required_route_is_exact (M : Interface v S I) (laws : AdapterLaws M)
    (s : State E C B U S) (a : Attempt B U)
    (h : (capture M s a).decision = .executed) :
    (a.root :: a.path).map v.owner = M.route s.control :=
  (execution_is_locally_admitted M laws s a h).2.2.exactRoute

theorem required_handoff_cannot_be_skipped (M : Interface v S I) (laws : AdapterLaws M)
    (s : State E C B U S) (a : Attempt B U)
    (h : (a.root :: a.path).map v.owner ≠ M.route s.control) :
    (capture M s a).decision ≠ .executed := by
  intro he
  exact h (required_route_is_exact M laws s a he)

theorem invalid_chain_never_executes (M : Interface v S I) (laws : AdapterLaws M)
    (s : State E C B U S) (a : Attempt B U)
    (h : ¬ ValueChain.Valid v (M.context s.control) a.root a.path) :
    (capture M s a).decision ≠ .executed := by
  intro he
  exact h (execution_is_locally_admitted M laws s a he).2.2.chain

/-- `current` is a semantic condition, not a published freshness algorithm. -/
theorem stale_basis_never_executes (M : Interface v S I) (laws : AdapterLaws M)
    (s : State E C B U S) (a : Attempt B U) (h : ¬ M.current s.control a.root) :
    (capture M s a).decision ≠ .executed := by
  intro he
  exact h (execution_is_locally_admitted M laws s a he).2.2.current

/-- Changing conditions cannot itself approve an execution. The revocation mechanism
is not specified; `reprofile_closes` is an explicit semantic obligation. -/
theorem reprofile_requires_revalidation (M : Interface v S I) (laws : AdapterLaws M)
    (s : State E C B U S) (c : C) (a : Attempt B U) :
    (capture M { s with control := M.reprofile s.control c } a).decision ≠ .executed := by
  intro he
  have ha := (execution_is_locally_admitted M laws _ a he).2.2
  exact laws.reprofile_closes s.control c a.root ha.available

/-- No successful semantic validation means no permission after that validation attempt. -/
theorem failed_revalidation_closes_gate (M : Interface v S I) (laws : AdapterLaws M)
    (s : State E C B U S) (i : I) (h : ∀ b, ¬ M.validates s.control i b)
    (a : Attempt B U) :
    (capture M { s with control := M.revalidate s.control i } a).decision ≠ .executed := by
  intro he
  have ha := (execution_is_locally_admitted M laws _ a he).2.2
  exact h a.root (laws.revalidate_origin s.control i a.root ha.available)

end Safety

namespace Accountability

def pruneExpired (now : Nat) (history : List (Record E C B U)) : List (Record E C B U) :=
  history.filter (fun r => decide (now ≤ r.attempt.retainUntil))

theorem no_early_deletion (now : Nat) (history : List (Record E C B U))
    (r : Record E C B U) (hMem : r ∈ history) (hTime : now ≤ r.attempt.retainUntil) :
    r ∈ pruneExpired now history := by
  simp [pruneExpired, hMem, hTime]

theorem every_attempt_is_recorded (M : Interface v S I) (s : State E C B U S)
    (a : Attempt B U) : capture M s a ∈ (advance M s a).history := by
  simp [advance]

end Accountability

namespace History

/-- Logical commands. The implementations of revalidation and reconfiguration are parameters. -/
inductive Command (C : Type uC) (B : Type uB) (U : Type uU) (I : Type uI) where
  | attempt (a : Attempt B U)
  | revalidate (input : I)
  | reprofile (context : C)
  | prune (cutoff : Nat)

def step (M : Interface v S I) (s : State E C B U S) : Command C B U I → State E C B U S
  | .attempt a => advance M s a
  | .revalidate i => { s with control := M.revalidate s.control i }
  | .reprofile c => { s with control := M.reprofile s.control c }
  | .prune t => { s with history := Accountability.pruneExpired t s.history }

def run (M : Interface v S I) (s : State E C B U S) : List (Command C B U I) → State E C B U S
  | [] => s
  | c :: cs => run M (step M s c) cs

def withoutPruning : List (Command C B U I) → List (Command C B U I)
  | [] => []
  | .prune _ :: cs => withoutPruning cs
  | c :: cs => c :: withoutPruning cs

def CutoffsWithin (now : Nat) : List (Command C B U I) → Prop
  | [] => True
  | .prune t :: cs => t ≤ now ∧ CutoffsWithin now cs
  | _ :: cs => CutoffsWithin now cs

theorem prune_twice (earlier later : Nat) (hTime : earlier ≤ later)
    (history : List (Record E C B U)) :
    Accountability.pruneExpired later (Accountability.pruneExpired earlier history) =
      Accountability.pruneExpired later history := by
  induction history with
  | nil => rfl
  | cons r rs ih =>
      by_cases hLater : later ≤ r.attempt.retainUntil
      · have hEarlier := Nat.le_trans hTime hLater
        simpa [Accountability.pruneExpired, hLater, hEarlier] using congrArg (List.cons r) ih
      · by_cases hEarlier : earlier ≤ r.attempt.retainUntil
        · simpa [Accountability.pruneExpired, hLater, hEarlier] using ih
        · simpa [Accountability.pruneExpired, hLater, hEarlier] using ih

def SameAt (now : Nat) (s t : State E C B U S) : Prop :=
  s.control = t.control ∧ s.halted = t.halted ∧
    Accountability.pruneExpired now s.history = Accountability.pruneExpired now t.history

private theorem advance_sameAt (M : Interface v S I) (now : Nat)
    (s t : State E C B U S) (h : SameAt now s t) (a : Attempt B U) :
    SameAt now (advance M s a) (advance M t a) := by
  have hCapture : capture M s a = capture M t a := by
    simp only [capture, h.1, h.2.1]
  refine ⟨h.1, ?_, ?_⟩
  · change (capture M s a).decision.isStopped = (capture M t a).decision.isStopped
    rw [hCapture]
  · change Accountability.pruneExpired now (capture M s a :: s.history) =
      Accountability.pruneExpired now (capture M t a :: t.history)
    have hHistory := h.2.2
    dsimp only [Accountability.pruneExpired] at hHistory
    simp only [Accountability.pruneExpired, List.filter_cons]
    rw [hCapture, hHistory]

/-- Exact list equality after arbitrary interleavings, including order and repetitions.
This proof does not need checker correctness or local handoff laws. -/
theorem run_without_pruning (M : Interface v S I) (now : Nat)
    (commands : List (Command C B U I)) :
    ∀ s t : State E C B U S, CutoffsWithin now commands → SameAt now s t →
      SameAt now (run M s commands) (run M t (withoutPruning commands)) := by
  induction commands with
  | nil => intro s t _ h; exact h
  | cons c cs ih =>
      intro s t hTime h
      cases c with
      | attempt a =>
          exact ih (advance M s a) (advance M t a) hTime (advance_sameAt M now s t h a)
      | prune cutoff =>
          apply ih (step M s (.prune cutoff)) t hTime.2
          exact ⟨h.1, h.2.1, (prune_twice cutoff now hTime.1 s.history).trans h.2.2⟩
      | reprofile context =>
          apply ih (step M s (.reprofile context)) (step M t (.reprofile context)) hTime
          exact ⟨congrArg (fun x => M.reprofile x context) h.1, h.2.1, h.2.2⟩
      | revalidate input =>
          apply ih (step M s (.revalidate input)) (step M t (.revalidate input)) hTime
          exact ⟨congrArg (fun x => M.revalidate x input) h.1, h.2.1, h.2.2⟩

/-- A semantic successful-validation event. This is NOT a concrete change ledger. -/
def validationAt (M : Interface v S I) (s : State E C B U S) : Command C B U I → B → Prop
  | .revalidate i => M.validates s.control i
  | _ => fun _ => False

/-- Existence of a validation occurrence within the supplied logical command prefix. -/
def Origin (M : Interface v S I) (s : State E C B U S)
    (commands : List (Command C B U I)) (b : B) : Prop :=
  match commands with
  | [] => False
  | c :: cs => validationAt M s c b ∨ Origin M (step M s c) cs b

private theorem step_available (M : Interface v S I) (laws : AdapterLaws M)
    (s : State E C B U S) (c : Command C B U I) (b : B)
    (h : M.available (step M s c).control b) :
    M.available s.control b ∨ validationAt M s c b := by
  cases c with
  | attempt a => exact Or.inl h
  | prune t => exact Or.inl h
  | reprofile context => exact False.elim (laws.reprofile_closes s.control context b h)
  | revalidate input => exact Or.inr (laws.revalidate_origin s.control input b h)

/-- Availability is traced back through commands; prior validation is not assumed per record. -/
theorem run_available_origin (M : Interface v S I) (laws : AdapterLaws M)
    (commands : List (Command C B U I)) :
    ∀ (s : State E C B U S) (b : B), M.available (run M s commands).control b →
      M.available s.control b ∨ Origin M s commands b := by
  induction commands with
  | nil => intro s b h; exact Or.inl h
  | cons c cs ih =>
      intro s b h
      rcases ih (step M s c) b h with hBefore | hLater
      · rcases step_available M laws s c b hBefore with hInitial | hHere
        · exact Or.inl hInitial
        · exact Or.inr (Or.inl hHere)
      · exact Or.inr (Or.inr hLater)

/-- The origin is an actual earlier command occurrence, not a future or unlocated assertion. -/
theorem origin_is_validation_occurrence (M : Interface v S I)
    (commands : List (Command C B U I)) (b : B) :
    ∀ s : State E C B U S, Origin M s commands b →
      ∃ before after input,
        commands = before ++ Command.revalidate input :: after ∧
        M.validates (run M s before).control input b := by
  induction commands with
  | nil => intro s h; exact False.elim h
  | cons c cs ih =>
      intro s h
      rcases h with hHere | hLater
      · cases c with
        | revalidate input => exact ⟨[], cs, input, rfl, hHere⟩
        | attempt a => exact False.elim hHere
        | reprofile context => exact False.elim hHere
        | prune cutoff => exact False.elim hHere
      · obtain ⟨before, after, input, hSplit, hIssued⟩ := ih (step M s c) hLater
        refine ⟨c :: before, after, input, ?_, hIssued⟩
        simpa only [List.cons_append] using congrArg (List.cons c) hSplit

/-- A record was captured at an identified command position. The state is used only
in the theorem witness, not stored or serialized into the public record. -/
def Produced (M : Interface v S I) (s : State E C B U S)
    (commands : List (Command C B U I)) (r : Record E C B U) : Prop :=
  ∃ before after a, commands = before ++ Command.attempt a :: after ∧
    r = capture M (run M s before) a

/-- Every surviving record is initial or has a capture occurrence in this execution. -/
theorem record_has_production (M : Interface v S I)
    (commands : List (Command C B U I)) :
    ∀ (s : State E C B U S) (r : Record E C B U), r ∈ (run M s commands).history →
      r ∈ s.history ∨ Produced M s commands r := by
  induction commands with
  | nil => intro s r h; exact Or.inl h
  | cons c cs ih =>
      intro s r h
      rcases ih (step M s c) r h with hHere | hLater
      · cases c with
        | attempt a =>
            change r ∈ capture M s a :: s.history at hHere
            rcases List.mem_cons.mp hHere with hEq | hOld
            · exact Or.inr ⟨[], cs, a, rfl, hEq⟩
            · exact Or.inl hOld
        | prune cutoff => exact Or.inl (List.mem_filter.mp hHere).1
        | reprofile context => exact Or.inl hHere
        | revalidate input => exact Or.inl hHere
      · obtain ⟨before, after, a, hSplit, hCaptured⟩ := hLater
        apply Or.inr
        refine ⟨c :: before, after, a, ?_, hCaptured⟩
        simpa only [List.cons_append] using congrArg (List.cons c) hSplit

theorem stopped_run_stays_stopped (M : Interface v S I)
    (commands : List (Command C B U I)) :
    ∀ s : State E C B U S, s.halted = true → (run M s commands).halted = true := by
  induction commands with
  | nil => intro s h; exact h
  | cons c cs ih =>
      intro s h
      apply ih (step M s c)
      cases c with
      | attempt a => exact Safety.stopped_state_remains_stopped M s a h
      | prune cutoff => exact h
      | reprofile context => exact h
      | revalidate input => exact h

/-- Returning to old context labels does not itself recreate permission. This does
NOT claim a particular receipt-freshness implementation after a later validation. -/
theorem profile_ABA_requires_revalidation (M : Interface v S I) (laws : AdapterLaws M)
    (s : State E C B U S) (other : C) (a : Attempt B U) :
    (capture M (run M s [.reprofile other, .reprofile (M.context s.control)]) a).decision ≠
      .executed := by
  exact Safety.reprofile_requires_revalidation M laws
    (step M s (.reprofile other)) (M.context s.control) a

theorem future_cutoff_counterexample (r : Record E C B U) :
    Accountability.pruneExpired r.attempt.retainUntil
        (Accountability.pruneExpired (r.attempt.retainUntil + 1) [r]) = [] ∧
      Accountability.pruneExpired r.attempt.retainUntil [r] = [r] := by
  simp [Accountability.pruneExpired]

end History

namespace Transparency

theorem recoverable_export_preserves_policy
    {V : Type uV} [Category.{vV} V] (publish : E ⥤ V) (recover : V ⥤ E)
    (hRoundTrip : publish ⋙ recover = 𝟭 E) (p : ResponsibilityOS.ObservationPolicy E) :
    ResponsibilityOS.PreservesPolicy publish p := by
  have hf : publish.Faithful :=
    ResponsibilityOS.IndexedAssurance.faithful_of_section recover publish hRoundTrip
  intro X Y f g hRelevant hEqual
  exact p.sound hRelevant (hf.map_injective hEqual)

/-- Two recoverable views are a sufficient construction, not a compulsory disclosure rule. -/
theorem composed_exports_preserve_policy
    {V : Type uV} [Category.{vV} V] {W : Type uW} [Category.{vW} W]
    (first : E ⥤ V) (firstBack : V ⥤ E) (hFirst : first ⋙ firstBack = 𝟭 E)
    (second : V ⥤ W) (secondBack : W ⥤ V) (hSecond : second ⋙ secondBack = 𝟭 V)
    (p : ResponsibilityOS.ObservationPolicy E) :
    ResponsibilityOS.PreservesPolicy (first ⋙ second) p := by
  have hf : first.Faithful :=
    ResponsibilityOS.IndexedAssurance.faithful_of_section firstBack first hFirst
  have hg : second.Faithful :=
    ResponsibilityOS.IndexedAssurance.faithful_of_section secondBack second hSecond
  intro X Y f g hRelevant hEqual
  exact p.sound hRelevant (hf.map_injective (hg.map_injective hEqual))

end Transparency

namespace Governance

/-- EU-level public metadata and supplied checks. This is not a private monitoring engine.
`current` is an externally justified applicability/freshness check, not a detector proved here. -/
structure MonitoringPlan (E : Type uE) [Category.{vE} E]
    (C : Type uC) (B : Type uB) (U : Type uU) where
  context : C
  documentContext : C
  version : Nat
  documentedVersion : Nat
  current : Record E C B U → Bool
  check : Record E C B U → Bool

variable [DecidableEq C]

def passesPlan (context : C) (plan : MonitoringPlan E C B U) (r : Record E C B U) : Bool :=
  decide (plan.context = context ∧ plan.documentContext = context ∧
    plan.version = plan.documentedVersion ∧ r.contextAt = context ∧
    r.decision = .executed) && (plan.current r && plan.check r)

def supportedRecords (context : C) (plan : MonitoringPlan E C B U)
    (history : List (Record E C B U)) : List (Record E C B U) :=
  history.filter (passesPlan context plan)

def reviewRecords (context : C) (plan : MonitoringPlan E C B U)
    (history : List (Record E C B U)) : List (Record E C B U) :=
  history.filter (fun r => !(passesPlan context plan r))

theorem monitoring_complete (context : C) (plan : MonitoringPlan E C B U)
    (history : List (Record E C B U)) (r : Record E C B U) (hMem : r ∈ history) :
    (r ∈ supportedRecords context plan history ∨ r ∈ reviewRecords context plan history) ∧
      ¬ (r ∈ supportedRecords context plan history ∧ r ∈ reviewRecords context plan history) := by
  cases h : passesPlan context plan r <;> simp [supportedRecords, reviewRecords, hMem, h]

theorem monitoring_preserves_occurrences (context : C) (plan : MonitoringPlan E C B U)
    (history : List (Record E C B U)) :
    (supportedRecords context plan history).length + (reviewRecords context plan history).length =
      history.length := by
  induction history with
  | nil => simp [supportedRecords, reviewRecords]
  | cons r rs ih =>
      cases h : passesPlan context plan r <;>
        simpa [supportedRecords, reviewRecords, h, Nat.add_comm, Nat.add_left_comm,
          Nat.add_assoc] using congrArg Nat.succ ih

theorem failed_predicate_is_reviewed (context : C) (plan : MonitoringPlan E C B U)
    (history : List (Record E C B U)) (r : Record E C B U)
    (hMem : r ∈ history) (hFail : passesPlan context plan r = false) :
    r ∈ reviewRecords context plan history := by
  simp [reviewRecords, hMem, hFail]

/-- A supplied negative currentness result cannot be silently cleared by another check. -/
theorem stale_evidence_requires_review (context : C) (plan : MonitoringPlan E C B U)
    (history : List (Record E C B U)) (r : Record E C B U)
    (hMem : r ∈ history) (hStale : plan.current r = false) :
    r ∈ reviewRecords context plan history := by
  apply failed_predicate_is_reviewed context plan history r hMem
  simp [passesPlan, hStale]

theorem changed_context_requires_review (context : C) (plan : MonitoringPlan E C B U)
    (history : List (Record E C B U)) (r : Record E C B U)
    (hMem : r ∈ history) (hChanged : r.contextAt ≠ context) :
    r ∈ reviewRecords context plan history := by
  apply failed_predicate_is_reviewed context plan history r hMem
  simp [passesPlan, hChanged]

theorem unmatched_plan_flags_all (context : C) (plan : MonitoringPlan E C B U)
    (history : List (Record E C B U)) (h : plan.version ≠ plan.documentedVersion) :
    supportedRecords context plan history = [] ∧ reviewRecords context plan history = history := by
  simp [supportedRecords, reviewRecords, passesPlan, h]

theorem outdated_document_flags_all (context : C) (plan : MonitoringPlan E C B U)
    (history : List (Record E C B U)) (h : plan.documentContext ≠ context) :
    supportedRecords context plan history = [] ∧ reviewRecords context plan history = history := by
  simp [supportedRecords, reviewRecords, passesPlan, h]

theorem current_support_document_binding (context : C) (plan : MonitoringPlan E C B U)
    (history : List (Record E C B U)) (r : Record E C B U)
    (h : r ∈ supportedRecords context plan history) :
    plan.context = context ∧ plan.documentContext = context ∧
      plan.version = plan.documentedVersion ∧ r.contextAt = context ∧
      r.decision = .executed ∧ plan.current r = true ∧ plan.check r = true := by
  have hp := (List.mem_filter.mp h).2
  have parts :
      (plan.context = context ∧ plan.documentContext = context ∧
        plan.version = plan.documentedVersion ∧ r.contextAt = context ∧
        r.decision = .executed) ∧ (plan.current r = true ∧ plan.check r = true) := by
    simpa [passesPlan] using hp
  exact ⟨parts.1.1, parts.1.2.1, parts.1.2.2.1, parts.1.2.2.2.1,
    parts.1.2.2.2.2, parts.2.1, parts.2.2⟩

end Governance

/-- Per-record CONCLUSION. The prefix witness establishes validation before this
capture. Its admission postcondition includes the exact historical actor route and
configured scope. No such certificate is required as an input event field. -/
structure ExecutionAssurance (M : Interface v S I)
    {V : Type uV} [Category.{vV} V] (start : State E C B U S)
    (commands : List (History.Command C B U I)) (publish : E ⥤ V)
    (r : Record E C B U) : Prop where
  priorValidation : ∃ before after a,
    commands = before ++ History.Command.attempt a :: after ∧
    r = capture M (History.run M start before) a ∧
    History.Origin M start before a.root ∧ Admission M (History.run M start before).control a
  permission : r.haltedBefore = false ∧ r.attempt.request = .allow ∧ r.ready = true
  rootBound : v.bound r.contextAt r.attempt.root
  everyStageBound : ∀ b ∈ r.attempt.root :: r.attempt.path, v.bound r.contextAt b
  rootScope : v.scope r.attempt.root r.attempt.use
  everyScope : ∀ b ∈ r.attempt.path, v.scope b r.attempt.use
  evidenceDistinction : ∀ g : (v.evidence r.attempt.root).source ⟶
      (v.evidence r.attempt.root).target,
    r.policyAt.relevant (v.evidence r.attempt.root).trace g →
      publish.map (v.evidence r.attempt.root).trace ≠ publish.map g

/-- Local contracts are lifted to a temporally located assurance witness for each execution. -/
theorem execution_has_prior_assurance (M : Interface v S I) (laws : AdapterLaws M)
    (handoffLaws : HandoffLaws v) (s : S) (hInitial : ∀ b, ¬ M.available s b)
    (commands : List (History.Command C B U I))
    {V : Type uV} [Category.{vV} V] (publish : E ⥤ V) (r : Record E C B U)
    (hMem : r ∈ (History.run M (initial s) commands).history)
    (hExecuted : r.decision = .executed)
    (hExport : ResponsibilityOS.PreservesPolicy publish r.policyAt) :
    ExecutionAssurance M (initial s) commands publish r := by
  have hProduced : History.Produced M (initial s) commands r := by
    rcases History.record_has_production M commands (initial s) r hMem with hOld | hNew
    · simp [initial] at hOld
    · exact hNew
  obtain ⟨before, after, a, hSplit, hCapture⟩ := hProduced
  subst r
  have ha := (Safety.execution_is_locally_admitted M laws _ a hExecuted).2.2
  have ho : History.Origin M (initial s) before a.root := by
    rcases History.run_available_origin M laws before (initial s) a.root ha.available with hOld | hNew
    · exact False.elim (hInitial a.root hOld)
    · exact hNew
  have hs := ValueChain.use_supported_at_every_handoff v handoffLaws
    (M.context (History.run M (initial s) before).control) a.root a.path ha.chain a.use ha.terminalUse
  refine ⟨⟨before, after, a, hSplit, rfl, ho, ha⟩, ?_, ha.binding, ?_, hs.1, hs.2, ?_⟩
  · exact Safety.execution_requires_permission
      (History.run M (initial s) before).halted
      (M.check (History.run M (initial s) before).control a) a.request hExecuted
  · exact ValueChain.every_stage_is_bound v handoffLaws _ a.root a.path ha.chain ha.binding
  · intro g hRelevant
    exact hExport hRelevant

/-- The history-wide conclusion, kept separate from the local adapter obligations. -/
structure HistoryAssurance [DecidableEq C] (M : Interface v S I) (s : S)
    (commands : List (History.Command C B U I)) (now : Nat)
    (plan : Governance.MonitoringPlan E C B U)
    {V : Type uV} [Category.{vV} V] (publish : E ⥤ V) : Prop where
  retained :
    Accountability.pruneExpired now (History.run M (initial s) commands).history =
      Accountability.pruneExpired now (History.run M (initial s) (History.withoutPruning commands)).history
  executions : ∀ r ∈ Accountability.pruneExpired now (History.run M (initial s) commands).history,
    r.decision = .executed → ExecutionAssurance M (initial s) commands publish r
  partition : ∀ r ∈ Accountability.pruneExpired now (History.run M (initial s) commands).history,
    let context := M.context (History.run M (initial s) commands).control
    let kept := Accountability.pruneExpired now (History.run M (initial s) commands).history
    (r ∈ Governance.supportedRecords context plan kept ∨ r ∈ Governance.reviewRecords context plan kept) ∧
      ¬ (r ∈ Governance.supportedRecords context plan kept ∧ r ∈ Governance.reviewRecords context plan kept)
  occurrenceCount :
    let context := M.context (History.run M (initial s) commands).control
    let kept := Accountability.pruneExpired now (History.run M (initial s) commands).history
    (Governance.supportedRecords context plan kept).length +
      (Governance.reviewRecords context plan kept).length = kept.length
  currentSupport : ∀ r ∈ Governance.supportedRecords
      (M.context (History.run M (initial s) commands).control) plan
      (Accountability.pruneExpired now (History.run M (initial s) commands).history),
    let context := M.context (History.run M (initial s) commands).control
    plan.context = context ∧ plan.documentContext = context ∧
      plan.version = plan.documentedVersion ∧ r.contextAt = context ∧
      r.decision = .executed ∧ plan.current r = true ∧ plan.check r = true
  failedChecks : ∀ r ∈ Accountability.pruneExpired now (History.run M (initial s) commands).history,
    Governance.passesPlan (M.context (History.run M (initial s) commands).control) plan r = false →
      r ∈ Governance.reviewRecords (M.context (History.run M (initial s) commands).control) plan
        (Accountability.pruneExpired now (History.run M (initial s) commands).history)

/-- Headline composition theorem. Local soundness, initial unavailability, in-range
pruning and historical-policy export correctness are EXPLICIT premises. The arbitrary
finite-history result, prior-validation witnesses, all-stage consequences, and lossless
partition are DERIVED. This is not verification of an undisclosed adapter implementation. -/
theorem no_silent_responsibility_gap [DecidableEq C]
    (M : Interface v S I) (laws : AdapterLaws M) (handoffLaws : HandoffLaws v)
    (s : S) (hInitial : ∀ b, ¬ M.available s b)
    (commands : List (History.Command C B U I)) (now : Nat)
    (hTime : History.CutoffsWithin now commands) (plan : Governance.MonitoringPlan E C B U)
    {V : Type uV} [Category.{vV} V] (publish : E ⥤ V)
    (hExport : ∀ r ∈ Accountability.pruneExpired now (History.run M (initial s) commands).history,
      r.decision = .executed → ResponsibilityOS.PreservesPolicy publish r.policyAt) :
    HistoryAssurance M s commands now plan publish := by
  have hSame := History.run_without_pruning M now commands (initial s) (initial s)
    hTime ⟨rfl, rfl, rfl⟩
  refine ⟨hSame.2.2, ?_, ?_, ?_, ?_, ?_⟩
  · intro r hMem hExecuted
    exact execution_has_prior_assurance M laws handoffLaws s hInitial commands publish r
      (List.mem_filter.mp hMem).1 hExecuted (hExport r hMem hExecuted)
  · intro r hMem
    exact Governance.monitoring_complete _ plan _ r hMem
  · exact Governance.monitoring_preserves_occurrences _ plan _
  · intro r hMem
    exact Governance.current_support_document_binding _ plan _ r hMem
  · intro r hMem hFail
    exact Governance.failed_predicate_is_reviewed _ plan _ r hMem hFail

/-- Recoverability is a sufficient alternative, not a requirement to disclose all information. -/
theorem no_silent_responsibility_gap_recoverable [DecidableEq C]
    (M : Interface v S I) (laws : AdapterLaws M) (handoffLaws : HandoffLaws v)
    (s : S) (hInitial : ∀ b, ¬ M.available s b)
    (commands : List (History.Command C B U I)) (now : Nat)
    (hTime : History.CutoffsWithin now commands) (plan : Governance.MonitoringPlan E C B U)
    {V : Type uV} [Category.{vV} V] (publish : E ⥤ V) (recover : V ⥤ E)
    (hRoundTrip : publish ⋙ recover = 𝟭 E) : HistoryAssurance M s commands now plan publish := by
  apply no_silent_responsibility_gap M laws handoffLaws s hInitial commands now hTime plan publish
  intro r _hMem _hExecuted
  exact Transparency.recoverable_export_preserves_policy publish recover hRoundTrip r.policyAt

namespace KernelConnection

variable {O : Type uO} [Category.{vO} O]

def standardEvidence (K : ResponsibilityOS.Kernel.{uO, vO, uF, vF} O)
    {X Y : O} (f : X ⟶ Y) : Evidence (ResponsibilityOS.responsibilityCategory K) where
  source := (ResponsibilityOS.standardTrace K).obj X
  target := (ResponsibilityOS.standardTrace K).obj Y
  trace := (ResponsibilityOS.standardTrace K).map f

theorem standard_evidence_keeps_operation (K : ResponsibilityOS.Kernel.{uO, vO, uF, vF} O)
    {X Y : O} (f : X ⟶ Y) : (standardEvidence K f).trace.base = f := by rfl

theorem standard_trace_preserves_policy (K : ResponsibilityOS.Kernel.{uO, vO, uF, vF} O)
    (p : ResponsibilityOS.ObservationPolicy O) :
    ResponsibilityOS.PreservesPolicy (ResponsibilityOS.standardTrace K) p := by
  intro X Y f g hRelevant hEqual
  exact p.sound hRelevant ((ResponsibilityOS.standard_trace_is_faithful K).map_injective hEqual)

/-- This is structural factorization, never executable replay. -/
theorem backward_audit_factorization (K : ResponsibilityOS.Kernel.{uO, vO, uF, vF} O)
    {X Y Z : O} (f : X ⟶ Y) (k : Z ⟶ X) (b : K.Fiber Y) (c : K.Fiber Z)
    (h : (⟨Z, c⟩ : ResponsibilityOS.responsibilityCategory K) ⟶ ⟨Y, b⟩)
    (hBase : h.base = k ≫ f) :
    ∃! (δ : (⟨Z, c⟩ : ResponsibilityOS.responsibilityCategory K) ⟶ ⟨X, (K.pull f).obj b⟩),
      δ.base = k ∧ δ ≫ ResponsibilityOS.IndexedAssurance.cartLift K f b = h := by
  exact ResponsibilityOS.backward_audit_factors_uniquely K f k b c h hBase

end KernelConnection

namespace Examples

open ResponsibilityOS.CollapseCounterexample

/-!
## Minimal existence witness

This deliberately degenerate model witnesses only that the local contracts are
inhabited and compatible with an actually retained execution and a nonempty
evidence policy. Context, basis, use, actor and validation input each have ONE
value; control has two values so reconfiguration can close admission.

There is no multi-actor route, business-use classification, receipt format,
validation-input parser, freshness/replay algorithm or production adapter here.
Route/scope/failure consequences remain the abstract theorems above. This example
is intentionally not a reference implementation for deployment.
-/

def view : Semantics EObj Unit Unit Unit Unit where
  evidence := fun _ => ⟨.src, .tgt, EHom.traceA⟩
  owner := fun _ => ()
  scope := fun _ _ => True
  bound := fun _ _ => True
  handoff := fun _ _ _ => True

theorem view_laws : HandoffLaws view := by
  constructor
  · intro c b d _h hb; exact hb
  · intro c b d _h u hu; exact hu

/-- A two-state existence witness, not a private admission/revocation algorithm.
Only the empty path is accepted; all substantive routes are handled abstractly. -/
def toy : Interface view Bool Unit where
  context := fun _ => ()
  policy := fun _ => tracePolicy
  route := fun _ => [()]
  permitted := fun _ _ => True
  available := fun s _ => s = true
  current := fun s _ => s = true
  revalidate := fun _ _ => true
  reprofile := fun _ _ => false
  validates := fun _ _ _ => True
  check := fun s a => match a.path with
    | [] => s
    | _ :: _ => false

theorem toy_laws : AdapterLaws toy := by
  constructor
  · intro s a h
    cases hp : a.path with
    | nil =>
        have hs : s = true := by simpa [toy, hp] using h
        refine ⟨hs, hs, True.intro, ?_, True.intro, True.intro, ?_⟩
        · simp [ValueChain.Valid, hp]
        · simp [toy, view, hp]
    | cons b bs => simp [toy, hp] at h
  · intro s i b _h; trivial
  · intro s c b h; cases h
  · intro s c; cases c; rfl

def useExample : Attempt Unit Unit :=
  ⟨(), [], (), .allow, 0, 0, Nat.le_refl 0⟩

def commands : List (History.Command Unit Unit Unit Unit) :=
  [.revalidate (), .attempt useExample]

theorem minimal_execution :
    (capture toy (History.run toy (initial false) [.revalidate ()]) useExample).decision =
      .executed := by rfl

/-- The positive execution is present in the retained history of this same run. -/
theorem retained_execution :
    capture toy (History.run toy (initial false) [.revalidate ()]) useExample ∈
      Accountability.pruneExpired 0 (History.run toy (initial false) commands).history := by
  change capture toy (initial true) useExample ∈ [capture toy (initial true) useExample]
  simp

def plan : Governance.MonitoringPlan EObj Unit Unit Unit :=
  ⟨(), (), 0, 0, fun _ => true, fun _ => true⟩

/-- Local laws, the headline conclusion, a retained execution, and a genuinely
nonempty policy coexist. No production-adapter correctness is asserted. -/
theorem nonvacuous_reference_chain :
    HistoryAssurance toy false commands 0 plan (𝟭 EObj) ∧
    capture toy (History.run toy (initial false) [.revalidate ()]) useExample ∈
      Accountability.pruneExpired 0 (History.run toy (initial false) commands).history ∧
    (capture toy (History.run toy (initial false) [.revalidate ()]) useExample).decision =
      .executed ∧ tracePolicy.relevant EHom.traceA EHom.traceB := by
  refine ⟨?_, retained_execution, minimal_execution,
    ResponsibilityOS.CollapseCounterexample.trace_policy_relevant⟩
  apply no_silent_responsibility_gap toy toy_laws view_laws false
    (by intro b h; cases h) commands 0 (by decide) plan (𝟭 EObj)
  intro r _hMem _hExecuted X Y f g hRelevant hEqual
  exact r.policyAt.sound hRelevant hEqual

theorem full_view_preserves_nonempty_trace_policy :
    ResponsibilityOS.PreservesPolicy (𝟭 EObj) tracePolicy ∧
      tracePolicy.relevant EHom.traceA EHom.traceB := by
  constructor
  · intro X Y f g hRelevant hEqual
    exact tracePolicy.sound hRelevant hEqual
  · exact ResponsibilityOS.CollapseCounterexample.trace_policy_relevant

theorem operation_only_view_fails : ¬ ResponsibilityOS.PreservesPolicy
    ResponsibilityOS.CollapseCounterexample.U tracePolicy :=
  ResponsibilityOS.CollapseCounterexample.U_does_not_preserve_trace_policy

end Examples

end JPAIGuidelinesMapping
