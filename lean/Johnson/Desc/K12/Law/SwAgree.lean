-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
import Johnson.Desc.K12.Law.SwUnfold
/-
Johnson/Desc/K12/Law/SwAgree.lean: THE THREE WRITES OF THE STEP BEHIND A SWITCH's SENDING (Tw.L9.switchBehind, Johnson/Top/H0/Tw/L9/Switch.lean) ARE YESES OF THE GROUND's PLAIN FUNCTIONS (Johnson/Desc/First/Base/Ground.lean): THREE AGREEMENT LEMMAS. BOOK-KEEPING. NO SOUNDNESS IS CLAIMED. NOTHING ON HIDING.
  shut_closeLedgerP   o < d.st.oracles.size ⇒ Ground.closeLedgerP d o = some { d with st := ‹d.st with o's ledger shut, as switchBehind writes it inline› }
  joinS_joinP         Tw.L9.joinS d.st g o kept = .ok S' ⇒ Ground.joinP d g o kept = some { d with st := S' }
  addRowS_addRowP     Tw.L9.addRowS d.st g row = .ok S' ⇒ Ground.addRowP d g row = some { d with st := S' }
WHY THEY HOLD: the switch's and the ground's texts follow one source, clause for clause: joinS's first guard (group and message are there) is joinL's first two clauses, its second (sampled; no test has begun) the next two, the other four one each; addRowS's second guard (no test has begun; no sample row) is two of rowL's clauses, the other six one each; the effects are the same terms.
WHAT FOR: whatever relation the ground's plain functions keep, the switch's step behind the sending keeps.
ONE WAY ONLY: that a yes of the plain function is a yes of the switch's text is not stated.
No sorry, no axiom of ours; each theorem has its premises; what each rests on is printed at the file's end.
-/
set_option autoImplicit false
namespace H2K.Sw
open OnBytes OnBytes.Params OnBytes.Slice
open VerifiableInference.Desc
open _root_.Desc.Plain (DState)

variable {L : Type}

theorem of_not_not {b : Bool} (h : ¬ (!b) = true) : b = true := by
  cases b
  · exact absurd rfl h
  · rfl

theorem shut_closeLedgerP (d : DState L) (o : Nat) (h : o < d.st.oracles.size) :
    Ground.closeLedgerP d o = some { d with st := { d.st with
      oracles := d.st.oracles.modify o fun x =>
        { x with ledger := x.ledger.map fun l => { l with closed := true } } } } := by
  unfold Ground.closeLedgerP
  rw [if_pos (by simp [Ground.closeLedgerL, Ground.ok, h])]
  rfl

theorem joinS_joinP (d : DState L) (g o : Nat) (kept : Bool) (S' : Statement)
    (h : Tw.L9.joinS d.st g o kept = .ok S') :
    Ground.joinP d g o kept = some { d with st := S' } := by
  unfold Tw.L9.joinS at h
  split at h
  · rename_i G x hG hx
    split at h
    · cases h
    · rename_i h18
      split at h
      · cases h
      · rename_i h19
        split at h
        · cases h
        · rename_i h20
          split at h
          · cases h
          · rename_i h21
            split at h
            · cases h
            · rename_i h22
              cases h
              unfold Ground.joinP
              have a18 : x.sampled = true ∧ G.inRun = false := by simpa using h18
              have a19 := of_not_not h19
              have a20 := of_not_not h20
              have a21 : G.members.contains o = false := Bool.eq_false_iff.2 h21
              have a22 := of_not_not h22
              rw [if_pos (by
                simp only [Ground.joinL, Ground.ok, Ground.has, hG, hx, List.all_cons, List.all_nil,
                  Option.isSome_some, Option.map_some, Option.getD_some, Bool.and_true,
                  Bool.and_eq_true]
                exact ⟨trivial, trivial, a18.1, by rw [a18.2]; rfl, a19, a20, by rw [a21]; rfl,
                  a22⟩), hG]
              rfl
  · cases h

theorem addRowS_addRowP (d : DState L) (g : Nat) (row : Row) (S' : Statement)
    (h : Tw.L9.addRowS d.st g row = .ok S') :
    Ground.addRowP d g row = some { d with st := S' } := by
  unfold Tw.L9.addRowS at h
  split at h
  · cases h
  · rename_i G hG
    split at h
    · cases h
    · rename_i h24
      split at h
      · cases h
      · rename_i h25
        split at h
        · cases h
        · rename_i h26
          split at h
          · cases h
          · rename_i h27
            split at h
            · cases h
            · rename_i h28
              split at h
              · cases h
              · rename_i h29
                cases h
                unfold Ground.addRowP
                rw [if_pos (by
                  simp only [Bool.not_eq_true, Bool.not_eq_false'] at h24 h25 h26 h27 h28 h29
                  simp only [Bool.and_eq_true] at h24
                  simp only [Ground.rowL, Ground.ok, Ground.has, hG, List.all_cons, List.all_nil,
                    Option.isSome_some, Option.map_some, Option.getD_some, Bool.and_true,
                    Bool.and_eq_true]
                  exact ⟨trivial, h24.1, h24.2, h25, h26, h27, h28, h29⟩)]
                rfl

end H2K.Sw

#print axioms H2K.Sw.shut_closeLedgerP
#print axioms H2K.Sw.joinS_joinP
#print axioms H2K.Sw.addRowS_addRowP
