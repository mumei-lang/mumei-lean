import Std

/-!
# Single-record authorization model

An independent model, not a bridge witness or a host-language sandbox.
Snapshots below are internal mathematical values, not transferable permissions.
-/

namespace MumeiLean.AuthorizationModel

inductive Role where
  | reader | writer | administrator | unknown
  deriving DecidableEq, Repr

inductive Field where
  | value | organization | owner | version | unknown
  deriving DecidableEq, Repr

inductive Operation where
  | read
  | update (field : Field) (value : Int)
  | unknown
  deriving DecidableEq, Repr

structure Principal where
  organization : Nat
  user : Nat
  role : Role
  deriving DecidableEq, Repr

structure Record where
  organization : Nat
  owner : Nat
  version : Nat
  value : Int
  deriving DecidableEq, Repr

structure Policy where
  revision : Nat
  readEnabled : Bool
  updateEnabled : Bool
  deriving DecidableEq, Repr

structure Proposal where
  target : Nat
  expectedVersion : Nat
  operation : Operation
  deriving DecidableEq, Repr

structure State where
  records : Nat → Option Record
  policy : Option Policy

def MayRead (p : Principal) : Prop :=
  p.role = .reader ∨ p.role = .writer ∨ p.role = .administrator

def MayUpdate (p : Principal) (r : Record) : Prop :=
  p.role = .administrator ∨ (p.role = .writer ∧ p.user = r.owner)

def Allowed (p : Principal) (r : Record) (policy : Policy) (q : Proposal) : Prop :=
  p.organization = r.organization ∧ q.expectedVersion = r.version ∧
    match q.operation with
    | .read => policy.readEnabled = true ∧ MayRead p
    | .update field _ => policy.updateEnabled = true ∧ field = .value ∧ MayUpdate p r
    | .unknown => False

instance (p : Principal) : Decidable (MayRead p) := by unfold MayRead; infer_instance
instance (p : Principal) (r : Record) : Decidable (MayUpdate p r) := by
  unfold MayUpdate; infer_instance
instance (p : Principal) (r : Record) (policy : Policy) (q : Proposal) :
    Decidable (Allowed p r policy q) := by
  unfold Allowed
  cases q.operation <;> infer_instance

structure Snapshot where
  principal : Principal
  proposal : Proposal
  record : Record
  policy : Policy

def prepare (s : State) (p : Principal) (q : Proposal) : Option Snapshot := do
  let r ← s.records q.target
  let policy ← s.policy
  if Allowed p r policy q then some ⟨p, q, r, policy⟩ else none

def Current (s : State) (p : Principal) (q : Proposal) (c : Snapshot) : Prop :=
  c.principal = p ∧ c.proposal = q ∧
  s.records q.target = some c.record ∧ s.policy = some c.policy ∧
  Allowed p c.record c.policy q

instance (s : State) (p : Principal) (q : Proposal) (c : Snapshot) :
    Decidable (Current s p q c) := by unfold Current; infer_instance

def replace (s : State) (target : Nat) (r : Record) : State :=
  { s with records := fun id => if id = target then some r else s.records id }

structure Outcome where
  state : State
  accepted : Bool
  value : Option Int

def reject (s : State) : Outcome := ⟨s, false, none⟩

private def applyOperation (s : State) (q : Proposal) (r : Record) : Outcome :=
  match q.operation with
  | .read => ⟨s, true, some r.value⟩
  | .update .value value =>
      ⟨replace s q.target { r with value := value, version := r.version + 1 }, true, none⟩
  | _ => reject s

def commit (s : State) (p : Principal) (q : Proposal) (c : Snapshot) : Outcome :=
  if Current s p q c then applyOperation s q c.record else reject s

def execute (s : State) (p : Principal) (q : Proposal) : Outcome :=
  match prepare s p q with
  | some c => commit s p q c
  | none => reject s

theorem commit_accepted_current (s : State) (p : Principal) (q : Proposal) (c : Snapshot)
    (h : (commit s p q c).accepted = true) : Current s p q c := by
  by_cases hc : Current s p q c
  · exact hc
  · simp [commit, hc, reject] at h

theorem accepted_authorized (s : State) (p : Principal) (q : Proposal)
    (h : (execute s p q).accepted = true) :
    ∃ r policy, s.records q.target = some r ∧ s.policy = some policy ∧ Allowed p r policy q := by
  unfold execute at h
  cases hp : prepare s p q with
  | none => simp [hp, reject] at h
  | some c =>
      rw [hp] at h
      have hc := commit_accepted_current s p q c h
      exact ⟨c.record, c.policy, hc.2.2.1, hc.2.2.2.1, hc.2.2.2.2⟩

theorem accepted_same_organization (s : State) (p : Principal) (q : Proposal)
    (h : (execute s p q).accepted = true) :
    ∃ r, s.records q.target = some r ∧ p.organization = r.organization := by
  obtain ⟨r, policy, hr, _, ha⟩ := accepted_authorized s p q h
  exact ⟨r, hr, ha.1⟩

theorem accepted_update_authority (s : State) (p : Principal) (q : Proposal)
    (field : Field) (value : Int) (hop : q.operation = .update field value)
    (h : (execute s p q).accepted = true) :
    ∃ r policy, s.records q.target = some r ∧ s.policy = some policy ∧
      policy.updateEnabled = true ∧ field = .value ∧ MayUpdate p r := by
  obtain ⟨r, policy, hr, hp, ha⟩ := accepted_authorized s p q h
  exact ⟨r, policy, hr, hp, by simpa [Allowed, hop] using ha.2.2⟩

theorem rejected_commit_unchanged (s : State) (p : Principal) (q : Proposal) (c : Snapshot)
    (h : (commit s p q c).accepted = false) :
    (commit s p q c).state = s ∧ (commit s p q c).value = none := by
  unfold commit at h ⊢
  split <;> simp_all [applyOperation, reject]
  split at h <;> simp_all [reject]

theorem rejected_unchanged (s : State) (p : Principal) (q : Proposal)
    (h : (execute s p q).accepted = false) :
    (execute s p q).state = s ∧ (execute s p q).value = none := by
  unfold execute at h ⊢
  split <;> simp_all [reject]
  exact rejected_commit_unchanged s p q _ h

theorem stale_record_rejected (s : State) (p : Principal) (q : Proposal) (c : Snapshot)
    (h : s.records q.target ≠ some c.record) : commit s p q c = reject s := by
  have hc : ¬ Current s p q c := fun hc => h hc.2.2.1
  simp [commit, hc]

theorem stale_policy_rejected (s : State) (p : Principal) (q : Proposal) (c : Snapshot)
    (h : s.policy ≠ some c.policy) : commit s p q c = reject s := by
  have hc : ¬ Current s p q c := fun hc => h hc.2.2.2.1
  simp [commit, hc]

theorem changed_principal_rejected (s : State) (p : Principal) (q : Proposal) (c : Snapshot)
    (h : c.principal ≠ p) : commit s p q c = reject s := by
  have hc : ¬ Current s p q c := fun hc => h hc.1
  simp [commit, hc]

theorem changed_proposal_rejected (s : State) (p : Principal) (q : Proposal) (c : Snapshot)
    (h : c.proposal ≠ q) : commit s p q c = reject s := by
  have hc : ¬ Current s p q c := fun hc => h hc.2.1
  simp [commit, hc]

def IdentityPreserved (before after : State) : Prop :=
  ∀ id, (after.records id).map (fun r => (r.organization, r.owner)) =
    (before.records id).map (fun r => (r.organization, r.owner))

theorem commit_preserves_identity (s : State) (p : Principal) (q : Proposal) (c : Snapshot) :
    IdentityPreserved s (commit s p q c).state := by
  intro id
  unfold commit
  split
  next hc =>
    cases hop : q.operation with
    | read => simp [applyOperation, hop]
    | unknown => simp [applyOperation, hop, reject]
    | update field value =>
        cases field <;> simp [applyOperation, hop, replace, reject]
        split
        next hi => simp [hi, hc.2.2.1]
        next => rfl
  next => rfl

theorem commit_preserves_other_record (s : State) (p : Principal) (q : Proposal) (c : Snapshot)
    (other : Nat) (h : other ≠ q.target) :
    (commit s p q c).state.records other = s.records other := by
  unfold commit
  split
  · cases hop : q.operation with
    | read => simp [applyOperation, hop]
    | unknown => simp [applyOperation, hop, reject]
    | update field value => cases field <;> simp [applyOperation, hop, replace, h, reject]
  · rfl

theorem execute_preserves_identity (s : State) (p : Principal) (q : Proposal) :
    IdentityPreserved s (execute s p q).state := by
  unfold execute
  split
  · exact commit_preserves_identity s p q _
  · intro id; rfl

theorem execute_preserves_other_record (s : State) (p : Principal) (q : Proposal)
    (other : Nat) (h : other ≠ q.target) :
    (execute s p q).state.records other = s.records other := by
  unfold execute
  split
  · exact commit_preserves_other_record s p q _ other h
  · rfl

theorem accepted_update_result (s : State) (p : Principal) (q : Proposal)
    (field : Field) (value : Int) (hop : q.operation = .update field value)
    (h : (execute s p q).accepted = true) :
    ∃ r, s.records q.target = some r ∧
      (execute s p q).state.records q.target =
        some { r with value := value, version := r.version + 1 } := by
  unfold execute at h ⊢
  cases hp : prepare s p q with
  | some c =>
    rw [hp] at h
    have hc := commit_accepted_current s p q c h
    have ha := hc.2.2.2.2.2.2
    simp only [hop] at ha
    have hf : field = .value := ha.2.1
    subst field
    exact ⟨c.record, hc.2.2.1, by simp [commit, hc, applyOperation, hop, replace]⟩
  | none => simp [hp, reject] at h

theorem accepted_read_result (s : State) (p : Principal) (q : Proposal)
    (hop : q.operation = .read) (h : (execute s p q).accepted = true) :
    (execute s p q).state = s ∧
      ∃ r, s.records q.target = some r ∧ (execute s p q).value = some r.value := by
  unfold execute at h ⊢
  cases hp : prepare s p q with
  | some c =>
    rw [hp] at h
    have hc := commit_accepted_current s p q c h
    simp [commit, hc, applyOperation, hop]
    exact ⟨c.record, hc.2.2.1, rfl⟩
  | none => simp [hp, reject] at h

theorem stale_version_rejected (s : State) (p : Principal) (q : Proposal) (c : Snapshot)
    (r : Record) (hr : s.records q.target = some r) (h : r.version ≠ c.record.version) :
    commit s p q c = reject s := by
  apply stale_record_rejected
  intro he
  rw [hr] at he
  exact h (congrArg Record.version (Option.some.inj he))

theorem replayed_update_rejected (s : State) (p : Principal) (q : Proposal)
    (field : Field) (value : Int) (hop : q.operation = .update field value)
    (h : (execute s p q).accepted = true) :
    (execute (execute s p q).state p q).accepted = false := by
  obtain ⟨r, hr, hafter⟩ := accepted_update_result s p q field value hop h
  obtain ⟨r', policy, hr', _, ha⟩ := accepted_authorized s p q h
  have heq : r' = r := Option.some.inj (hr'.symm.trans hr)
  subst r'
  cases hb : (execute (execute s p q).state p q).accepted with
  | false => rfl
  | true =>
      obtain ⟨r'', policy'', hr'', _, ha''⟩ := accepted_authorized _ p q hb
      have heq := Option.some.inj (hafter.symm.trans hr'')
      have hv : r.version = r.version + 1 := by
        simpa [heq.symm, ha.2.1] using ha''.2.1
      exact False.elim (Nat.ne_of_lt (Nat.lt_succ_self r.version) hv)

theorem execute_preserves_policy (s : State) (p : Principal) (q : Proposal) :
    (execute s p q).state.policy = s.policy := by
  unfold execute
  split
  · unfold commit
    split
    · cases hop : q.operation with
      | read => simp [applyOperation, hop]
      | unknown => simp [applyOperation, hop, reject]
      | update field value => cases field <;> simp [applyOperation, hop, replace, reject]
    · rfl
  · rfl

def run (s : State) : List (Principal × Proposal) → State
  | [] => s
  | (p, q) :: rest => run (execute s p q).state rest

theorem finite_run_preserves_identity (s : State) (requests : List (Principal × Proposal)) :
    IdentityPreserved s (run s requests) := by
  induction requests generalizing s with
  | nil => intro id; rfl
  | cons request rest ih =>
      rcases request with ⟨p, q⟩
      intro id
      exact (ih (execute s p q).state id).trans (execute_preserves_identity s p q id)

def TraceAuthorized (s : State) : List (Principal × Proposal) → Prop
  | [] => True
  | (p, q) :: rest =>
      ((execute s p q).accepted = true →
        ∃ r policy, s.records q.target = some r ∧ s.policy = some policy ∧ Allowed p r policy q) ∧
      TraceAuthorized (execute s p q).state rest

theorem finite_trace_authorized (s : State) (requests : List (Principal × Proposal)) :
    TraceAuthorized s requests := by
  induction requests generalizing s with
  | nil => trivial
  | cons request rest ih =>
      rcases request with ⟨p, q⟩
      exact ⟨accepted_authorized s p q, ih _⟩

end MumeiLean.AuthorizationModel
