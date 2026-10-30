-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/GoodSendPlaces.lean: the blocks that stand at the kind's places on the first
chain, as the places' own text makes them, are sendings in the sense of the law in the form of the
rule of composition (IsSend, GoodSend3.lean), and leave the older messages (KeepsOld,
GoodSend5.lean): a segment's later moment, W's sending, and a later moment with the quiet step
behind the reads laid behind it.

Main names (parLater and parW are Johnson/Desc/K1/Places.lean's): isSend_laterAt, isSend_wAt,
keepsOld_laterAt, keepsOld_wAt;
leaves_layers, leaves_head; isSend_reads_layers, isSend_reads_head, keepsOld_reads_layers,
keepsOld_reads_head. The first segment's opening: isSend_firstAtS, keepsOld_firstAtS.

What is not claimed. Which of these blocks a file's description seats at which place is not said
here. The law's other premises are not met here. Nothing on soundness of a protocol, on an honest
prover or on hiding.

-/
import Johnson.Desc.K1.Law.GoodSend5
import Johnson.Desc.K8.ReadsQuietLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model Desc.Plain
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K8 (ReadsQuiet.layers ReadsQuiet.head ReadsQuiet.PG ReadsQuiet.PH)

variable {Cl : Type}

theorem isSend_laterAt (q : Params.First) (gp : GPar) (link piece moment : Nat)
    (arrays : Option (List Nat)) :
    IsSend (parLater q gp link piece moment) (fun s : S => s.st)
      (laterAt q gp link piece moment arrays : Block S Cl) :=
  isSend_commitAtS _ _ _ _

theorem keepsOld_laterAt (q : Params.First) (gp : GPar) (link piece moment : Nat)
    (arrays : Option (List Nat)) :
    KeepsOld (fun s : S => s.st) (laterAt q gp link piece moment arrays : Block S Cl) :=
  keepsOld_commitAtS _ _ _ _

theorem isSend_wAt (q : Params.First) (gp : GPar) (piece : Nat) (b : Block S Cl)
    (h : wAt q gp piece = some b) :
    ∃ msg, linMessageW q.lin = some msg ∧ IsSend (parW q gp piece msg) (fun s : S => s.st) b ∧
      KeepsOld (fun s : S => s.st) b := by
  obtain ⟨msg, hm, rfl⟩ := Option.map_eq_some_iff.1 h
  exact ⟨msg, hm, isSend_sendAtS _, keepsOld_sendAtS _⟩

/-- The quiet step behind a layer's reads leaves the statement. -/
theorem leaves_layers (G : ReadsQuiet.PG) : LeavesMsgs (fun s : S => s.st) (ReadsQuiet.layers G) :=
  fun s s' _ _ h => by
    show SameMsgs s.st s'.st
    rw [(K8.ReadsQuiet.layers_frame h).2.2.1]
    exact ⟨rfl, fun _ => rfl⟩

/-- The quiet step behind the head's reads leaves the statement. -/
theorem leaves_head (H : ReadsQuiet.PH) : LeavesMsgs (fun s : S => s.st) (ReadsQuiet.head H) :=
  fun s s' _ _ h => by
    show SameMsgs s.st s'.st
    rw [(K8.ReadsQuiet.head_frame h).2.2.1]
    exact ⟨rfl, fun _ => rfl⟩

/-- **The reads' place of a layer.** -/
theorem isSend_reads_layers (q : Params.First) (gp : GPar) (link piece moment : Nat)
    (arrays : Option (List Nat)) (name : String) (G : ReadsQuiet.PG) :
    IsSend (parLater q gp link piece moment) (fun s : S => s.st)
      ((laterAt q gp link piece moment arrays).andThen name (ReadsQuiet.layers G)) :=
  isSend_andThen _ _ _ _ _ (isSend_laterAt q gp link piece moment arrays) rfl (leaves_layers G)

/-- **The reads' place of the head.** -/
theorem isSend_reads_head (q : Params.First) (gp : GPar) (link piece moment : Nat)
    (arrays : Option (List Nat)) (name : String) (H : ReadsQuiet.PH) :
    IsSend (parLater q gp link piece moment) (fun s : S => s.st)
      ((laterAt q gp link piece moment arrays).andThen name (ReadsQuiet.head H)) :=
  isSend_andThen _ _ _ _ _ (isSend_laterAt q gp link piece moment arrays) rfl (leaves_head H)

theorem keepsOld_reads_layers (q : Params.First) (gp : GPar) (link piece moment : Nat)
    (arrays : Option (List Nat)) (name : String) (G : ReadsQuiet.PG) :
    KeepsOld (fun s : S => s.st)
      ((laterAt q gp link piece moment arrays).andThen name (ReadsQuiet.layers G)) :=
  keepsOld_andThen _ _ _ _ (keepsOld_laterAt q gp link piece moment arrays)
    (keepsOld_of_leaves _ _ (leaves_layers G))

theorem keepsOld_reads_head (q : Params.First) (gp : GPar) (link piece moment : Nat)
    (arrays : Option (List Nat)) (name : String) (H : ReadsQuiet.PH) :
    KeepsOld (fun s : S => s.st)
      ((laterAt q gp link piece moment arrays).andThen name (ReadsQuiet.head H)) :=
  keepsOld_andThen _ _ _ _ (keepsOld_laterAt q gp link piece moment arrays)
    (keepsOld_of_leaves _ _ (leaves_head H))

end VerifiableInference.Desc.K1
