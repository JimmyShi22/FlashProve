-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
import Johnson.Desc.K12.Law.FreeOfMade
import Johnson.Desc.K12.Law.TreesNumber
/-
Johnson/Desc/K12/Law/FirstTreeOfMade.lean: THE NUMBER «firstTree» OF A PROXIMITY TEST's FOUR PLACES, AS THE MAKER LAYS IT (placesOfMade, Johnson/Desc/K12/Plan/PlaceOfPlan.lean): 0 at the three places on the first and the shared chain; at the last chain's own test: THE ROOTS THAT THE FIRST CHAIN's DECLARED ROUNDS HOLD, AND ONE. It reads the plan and the makers alone. BOOK-KEEPING. NO SOUNDNESS IS CLAIMED. NOTHING ON HIDING.
  treesSent_length    treesSent at_ c P extra = .ok ts ⇒ ts.length = (P.rounds.map (·.roots)).sum: as many trees as the plan's rounds have roots
  later_firstTree · places_firstTree   placesOfMade m = .ok X ⇒ X.L | X.U | X.O's nums.firstTree = 0 ∧ ∃ t0, treesSent "proof file, first chain" … = .ok t0 ∧ X.W.nums.firstTree = t0.length + 1
  firstTree_W         placesOfMade m = .ok X · declPOf m = .ok D ⇒ X.W.nums.firstTree = rootsOf D.1 + 1
No premise on the made plans: the trees and the declared rounds are both made over the plan as read back.
No sorry, no axiom of ours; each theorem has its premises; what each rests on is printed at the file's end.
-/
set_option autoImplicit false
namespace H2K.Made
open OnBytes OnBytes.Params Johnson.G.OfPlan
open H2U (placesOfMade placesLater laterOfProof mkPlace Places4 PlaceNums Later3 LaterArgs
  firstsOfPlan)

theorem treesSent_length {at_ : String} {c : Johnson.G.ChainSends} {P : Fmt.Plan}
    {extra : List Sent} {ts : List (Sent × Nat)} (h : treesSent at_ c P extra = .ok ts) :
    ts.length = (P.rounds.map (·.roots)).sum := by
  have hf := fun t n hm => treesSent_front h P.rounds.length (Nat.le_refl _) t n hm
  rw [List.take_length] at hf
  unfold treesSent at h
  dsimp only at h
  cases hl : c.sends.mapM (sentAt at_ c.codes (P.entries.length - P.rounds.length)) with
  | error e => rw [hl] at h; cases h
  | ok l =>
    rw [hl] at h
    simp only [bind, Except.bind] at h
    split at h
    · cases h
    · rename_i hfind
      split at h
      swap
      · cases h
      · rename_i hall
        cases h
        rw [List.length_zipIdx]
        have hc : ((l.flatten ++ extra).mergeSort fun a b => decide (a.round ≤ b.round)).countP
            (fun t => decide (t.round < P.rounds.length)) =
            ((l.flatten ++ extra).mergeSort fun a b => decide (a.round ≤ b.round)).length :=
          List.countP_eq_length.2 fun t ht => List.all_eq_true.1 hall t ht
        rw [← hc, countP_lt_sum _ P.rounds ?_ P.rounds.length (Nat.le_refl _), List.take_length]
        intro j e he
        have hj : j < P.rounds.length := (List.getElem?_eq_some_iff.1 he).1
        have h0 := List.find?_eq_none.1 hfind (e, j)
          (List.mem_zipIdx_iff_getElem?.2 (by simpa using he))
        simp only [bne_iff_ne, ne_eq, Decidable.not_not] at h0
        rw [made_getD _ _ j (by rw [Array.size_replicate]; exact hj)] at h0
        simpa [Array.getD_eq_getD_getElem?, hj] using h0

theorem later_firstTree (A : LaterArgs) (X : Later3) (h : placesLater A = .ok X) :
    X.U.nums.firstTree = 0 ∧ (∀ o, X.O = some o → o.nums.firstTree = 0) ∧
      ∃ t0, treesSent (A.file ++ ", first chain") A.c0 A.P0 [] = .ok t0 ∧
        X.W.nums.firstTree = t0.length + 1 := by
  unfold placesLater at h
  dsimp only at h
  obtain ⟨t0, h0, h⟩ := bind_ok h
  obtain ⟨t1, _, h⟩ := bind_ok h
  obtain ⟨t2, _, h⟩ := bind_ok h
  obtain ⟨fU, _, h⟩ := bind_ok h
  obtain ⟨fW, _, h⟩ := bind_ok h
  obtain ⟨tU, _, h⟩ := bind_ok h
  obtain ⟨tW, _, h⟩ := bind_ok h
  obtain rfl := Except.ok.inj h
  refine ⟨rfl, ?_, t0, h0, rfl⟩
  intro o ho
  dsimp only at ho
  split at ho
  · rename_i tO fO h1 h2
    cases ho
    show fO.2 = 0
    split at h2
    · obtain ⟨x, _, rfl⟩ := Option.map_eq_some_iff.1 h2
      rfl
    · cases h2
  · cases ho

theorem firsts_L (m : Made) (Fs : H2U.Firsts) (h : firstsOfPlan m = .ok Fs) : Fs.L.2 = 0 := by
  unfold firstsOfPlan at h
  dsimp only at h
  obtain ⟨t0, _, h⟩ := bind_ok h
  obtain ⟨t1, _, h⟩ := bind_ok h
  obtain ⟨t2, _, h⟩ := bind_ok h
  obtain ⟨l, _, h⟩ := bind_ok h
  obtain ⟨u, _, h⟩ := bind_ok h
  obtain ⟨w, _, h⟩ := bind_ok h
  obtain rfl := Except.ok.inj h
  rfl

theorem places_firstTree (m : Made) (X : Places4) (h : placesOfMade m = .ok X) :
    X.L.nums.firstTree = 0 ∧ X.U.nums.firstTree = 0 ∧ (∀ o, X.O = some o → o.nums.firstTree = 0) ∧
      ∃ t0, treesSent "proof file, first chain" m.proof.1
          m.p.chains.proof.first.given.plan [] = .ok t0 ∧ X.W.nums.firstTree = t0.length + 1 := by
  unfold placesOfMade at h
  dsimp only at h
  obtain ⟨Fs, hFs, h⟩ := bind_ok h
  obtain ⟨tL, _, h⟩ := bind_ok h
  obtain ⟨X3, hX3, h⟩ := bind_ok h
  obtain ⟨rows, _, h⟩ := bind_ok h
  obtain rfl := Except.ok.inj h
  obtain ⟨a, b, c⟩ := later_firstTree _ X3 hX3
  exact ⟨firsts_L m Fs hFs, a, b, c⟩


theorem firstTree_W (m : Made) (X : Places4) (D : Decl3) (hX : placesOfMade m = .ok X)
    (hD : declPOf m = .ok D) : X.W.nums.firstTree = rootsOf D.1 + 1 := by
  obtain ⟨_, _, _, t0, h0, e⟩ := places_firstTree m X hX
  unfold declPOf at hD
  obtain ⟨d0, _, _⟩ := fileOf_entries hD
  rw [e, treesSent_length h0, ← d0]
  unfold rootsOf
  rw [List.map_map]
  rfl

end H2K.Made

#print axioms H2K.Made.treesSent_length
#print axioms H2K.Made.places_firstTree
#print axioms H2K.Made.firstTree_W
