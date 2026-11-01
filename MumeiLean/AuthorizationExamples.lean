import MumeiLean.AuthorizationModel

namespace MumeiLean.AuthorizationExamples

open AuthorizationModel

def record : Record := ⟨7, 10, 3, 40⟩
def policy : Policy := ⟨1, true, true⟩
def initial : State := ⟨fun id => if id = 1 then some record else none, some policy⟩
def writer : Principal := ⟨7, 10, .writer⟩
def update : Proposal := ⟨1, 3, .update .value 50⟩
def read : Proposal := ⟨1, 3, .read⟩
def snapshot : Snapshot := ⟨writer, update, record, policy⟩

theorem owner_update_succeeds : (execute initial writer update).accepted = true := by decide
theorem read_succeeds : (execute initial ⟨7, 11, .reader⟩ read).value = some 40 := by decide
theorem administrator_update_succeeds :
    (execute initial ⟨7, 11, .administrator⟩ update).accepted = true := by decide
theorem update_changes_value_and_version :
    (execute initial writer update).state.records 1 = some ⟨7, 10, 4, 50⟩ := by decide
theorem repeated_update_rejected :
    (execute (execute initial writer update).state writer update).accepted = false := by decide
theorem next_version_succeeds :
    (execute (execute initial writer update).state writer
      { update with expectedVersion := 4 }).accepted = true := by decide
theorem read_is_repeatable :
    (execute (execute initial writer read).state writer read).value = some 40 := by decide
theorem missing_record_rejected :
    (execute initial writer { update with target := 2 }).accepted = false := by decide
theorem missing_policy_rejected :
    (execute { initial with policy := none } writer update).accepted = false := by decide
theorem empty_store_rejected :
    (execute ⟨fun _ => none, some policy⟩ writer update).accepted = false := by decide
theorem stale_version_rejected :
    (execute initial writer { update with expectedVersion := 2 }).accepted = false := by decide
theorem future_version_rejected :
    (execute initial writer { update with expectedVersion := 4 }).accepted = false := by decide
theorem unknown_operation_rejected :
    (execute initial writer { update with operation := .unknown }).accepted = false := by decide

theorem protected_fields_rejected :
    [Field.organization, .owner, .version, .unknown].all (fun field =>
      !(execute initial writer { update with operation := .update field 50 }).accepted) = true := by
  decide

theorem protected_fields_rejected_for_administrator :
    [Field.organization, .owner, .version, .unknown].all (fun field =>
      !(execute initial ⟨7, 11, .administrator⟩
        { update with operation := .update field 50 }).accepted) = true := by decide

theorem changed_target_rejected :
    (commit initial writer { update with target := 2 } snapshot).accepted = false := by decide
theorem changed_value_rejected :
    (commit initial writer { update with operation := .update .value 51 } snapshot).accepted =
      false := by decide
theorem changed_field_rejected :
    (commit initial writer { update with operation := .update .owner 51 } snapshot).accepted =
      false := by decide
theorem changed_operation_rejected :
    (commit initial writer read snapshot).accepted = false := by decide
theorem changed_principal_rejected :
    (commit initial ⟨7, 11, .administrator⟩ update snapshot).accepted = false := by decide
theorem changed_record_value_rejected :
    (commit (replace initial 1 { record with value := 99 }) writer update snapshot).accepted =
      false := by decide
theorem changed_record_version_rejected :
    (commit (replace initial 1 { record with version := 4 }) writer update snapshot).accepted =
      false := by decide
theorem changed_record_organization_rejected :
    (commit (replace initial 1 { record with organization := 8 }) writer update snapshot).accepted =
      false := by decide
theorem changed_record_owner_rejected :
    (commit (replace initial 1 { record with owner := 11 }) writer update snapshot).accepted =
      false := by decide
theorem changed_policy_revision_rejected :
    (commit { initial with policy := some { policy with revision := 2 } }
      writer update snapshot).accepted = false := by decide
theorem disabled_updates_rejected :
    (execute { initial with policy := some { policy with updateEnabled := false } }
      writer update).accepted = false := by decide
theorem disabled_reads_rejected :
    (execute { initial with policy := some { policy with readEnabled := false } }
      writer read).accepted = false := by decide
theorem removed_policy_rejected :
    (commit { initial with policy := none } writer update snapshot).accepted = false := by decide
theorem removed_record_rejected :
    (commit ⟨fun _ => none, some policy⟩ writer update snapshot).accepted = false := by decide
theorem unrelated_record_preserved :
    (execute (replace initial 2 ⟨8, 11, 9, 99⟩) writer update).state.records 2 =
      some ⟨8, 11, 9, 99⟩ := by decide
theorem mixed_trace_result :
    (run initial [(writer, update), (⟨8, 10, .administrator⟩, update),
      (writer, { update with expectedVersion := 4, operation := .update .value 60 })]).records 1 =
        some ⟨7, 10, 5, 60⟩ := by decide

structure RoleCase where
  role : Role
  canRead : Bool
  canUpdateOwn : Bool
  canUpdateOther : Bool

def roleCases : List RoleCase :=
  [⟨.reader, true, false, false⟩, ⟨.writer, true, true, false⟩,
   ⟨.administrator, true, true, true⟩, ⟨.unknown, false, false, false⟩]

/-- 128 decisions: four roles, two organizations, two owners, read/update, enabled/disabled. -/
theorem decision_matrix :
    roleCases.all (fun c => [7, 8].all (fun organization => [10, 11].all (fun owner =>
      [false, true].all (fun enabled => [false, true].all (fun isUpdate =>
        let p : Principal := ⟨organization, owner, c.role⟩
        let s : State := { initial with policy := some ⟨1, enabled, enabled⟩ }
        let q := if isUpdate then update else read
        let permitted := if isUpdate then
          (if owner == 10 then c.canUpdateOwn else c.canUpdateOther) else c.canRead
        (execute s p q).accepted == (enabled && organization == 7 && permitted)))))) = true := by
  decide

end MumeiLean.AuthorizationExamples
