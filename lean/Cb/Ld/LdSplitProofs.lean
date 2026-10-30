-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdSplitProofs.lean: the proofs of the statements of Cb/Ld/LdSplit.lean (a row on two groups is
split by one mask entry).
Named tools: `addAt_holds` (what a row with a changed coefficient says), `SplitAt.msg_put_ne`,
`SplitAt.val_put` (the messages with the entry overwritten), `SplitAt.slf_val_put` (a form that does
not read the entry does not see the change). Nothing is defined here that a statement reads.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdSplit
import Cb.Ld.LdBatSigProofs
import Prob.Linear

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Cb.Ood IOR

theorem ldSpl_say : Spec.ldSpl_say := by
  intro K X X' W Pl d nx Ex val A B hfw hon hcore hbw
  refine ⟨⟨((Blocks.plainPoint Pl Unit d, ()) : (sayRound Pl d).IsPoint × Unit)⟩,
    ⟨fun x y y' τ τ' _ hpl _ _ => ?_,
      fun y y' τ τ' p _ _ hE _ => hE p (Finset.mem_singleton_self p)⟩,
    fun x y w c ρ hR _ => ⟨rfl, hfw x y w hR⟩,
    ?_,
    fun w x c ρ => hcore w,
    prRho_empty _ fun _ h => h,
    fun _ _ => le_refl _,
    fun _ => prRho_empty _ fun _ h => h,
    ?_⟩
  · have e : said τ = said τ' :=
      congrArg (fun r : Plains [sayRound Pl d] => (show Pl × Unit from r).1) hpl
    show some (nx x (said τ)) = some (nx x (said τ'))
    rw [e]
  · intro a τ b ha hb
    obtain ⟨h1, h2⟩ := red_out_eq_some.1 hb
    have e : b = (nx a.1 (said τ), a.2) := Prod.ext (Option.some.inj h1).symm h2
    rw [e]
    exact hon a.1 a.2 _ ha
  · intro a ha m
    refine Nat.le_of_eq (cnt_false fun c hc => hc fun b w hb hw => ?_)
    obtain ⟨h1, h2⟩ := red_out_eq_some.1 hb
    have e : b = (nx a.1 m.2, a.2) := Prod.ext (Option.some.inj h1).symm h2
    rw [e] at hw
    exact hbw a.1 a.2 _ w ha hw

section Tools
variable {E : Type} [Field E]

theorem addAt_holds {St J : Type} [Fintype J] [DecidableEq J] (sl : Slf E St J) (c : E) (κ : J)
    (t : E) (st : St) (u : J → E) :
    (sl.addAt c κ).Holds (t, st) u ↔ sl.val st u + c * u κ = t := by
  have h : ∑ j, sl.addAt c κ st j * u j = sl.val st u + c * u κ := by
    simp [Slf.addAt, Slf.val, add_mul, Finset.sum_add_distrib]
  exact ⟨fun h1 => h.symm.trans h1, fun h1 => h.trans h1⟩

variable {S : Sig E} {G₁ G₂ : Grp S} (k : SplitAt G₁ G₂)

omit [Field E] in
theorem SplitAt.val_put (u : E) (m : S.Msg) : k.val (k.put u m) = u := by
  simp [SplitAt.val, SplitAt.put]

omit [Field E] in
theorem SplitAt.msg_put_ne (G : Grp S) (h : G.mem k.o) (u : E) (m : S.Msg)
    (n : G.C.J) (hn : n ≠ ⟨⟨k.o, h⟩, k.j⟩) :
    G.msg (k.put u m) n = G.msg m n := by
  obtain ⟨⟨o, h'⟩, j⟩ := n
  by_cases ho : o = k.o
  · subst ho
    have hj : j ≠ k.j := fun e => hn (by rw [e])
    simp [Grp.msg, SplitAt.put, hj]
  · simp [Grp.msg, SplitAt.put, ho]

theorem SplitAt.slf_val_put (G : Grp S) (h : G.mem k.o) {St : Type} (sl : Slf E St G.C.J) (st : St)
    (h0 : sl st ⟨⟨k.o, h⟩, k.j⟩ = 0) (u : E) (m : S.Msg) :
    sl.val st (G.msg (k.put u m)) = sl.val st (G.msg m) := by
  refine Finset.sum_congr rfl fun n _ => ?_
  by_cases hn : n = ⟨⟨k.o, h⟩, k.j⟩
  · rw [hn, h0, zero_mul, zero_mul]
  · rw [k.msg_put_ne G h u m n hn]

theorem Grp.slf_val_cut (G : Grp S) (Rd : S.Ent → Prop) [DecidablePred Rd] {St : Type}
    (sl : Slf E St G.C.J) (st : St) (h : ∀ n, ¬ Rd (G.ent n) → sl st n = 0) (m : S.Msg) :
    sl.val st (G.msg (S.cut Rd m)) = sl.val st (G.msg m) := by
  refine Finset.sum_congr rfl fun n _ => ?_
  by_cases hn : Rd (G.ent n)
  · have e : G.msg (S.cut Rd m) n = G.msg m n := if_pos hn
    rw [e]
  · rw [h n hn, zero_mul, zero_mul]

end Tools

theorem ldSpl_sum : Spec.ldSpl_sum := by
  intro E _ _ S G₁ G₂ k St₁ St₂ sl₁ sl₂ τ st₁ st₂ m
  have e1 : G₁.msg m k.e₁ = k.val m := rfl
  have e2 : G₂.msg m k.e₂ = k.val m := rfl
  constructor
  · rintro t ⟨h1, h2⟩
    have a1 := (addAt_holds sl₁ 1 k.e₁ t st₁ (G₁.msg m)).1 h1
    have a2 := (addAt_holds sl₂ (-1) k.e₂ (τ - t) st₂ (G₂.msg m)).1 h2
    rw [e1] at a1
    rw [e2] at a2
    show sl₁.val st₁ (G₁.msg m) + sl₂.val st₂ (G₂.msg m) = τ
    linear_combination a1 + a2
  · intro h
    have h' : sl₁.val st₁ (G₁.msg m) + sl₂.val st₂ (G₂.msg m) = τ := h
    refine ⟨(addAt_holds sl₁ 1 k.e₁ _ st₁ (G₁.msg m)).2 ?_,
      (addAt_holds sl₂ (-1) k.e₂ _ st₂ (G₂.msg m)).2 ?_⟩
    · rw [e1]
      unfold splitVal
      ring
    · rw [e2]
      unfold splitVal
      linear_combination h'

theorem ldSpl_good : Spec.ldSpl_good := by
  intro E Kc St₀ Wp _ _ S G₁ G₂ k St₁ St₂ sl₁ sl₂ E₀ A₀ Rd _ h0 h0' hr hr' hk
  have hv : ∀ (m : S.Msg), k.val (S.cut Rd m) = k.val m := fun m => if_pos hk
  refine ⟨ldSpl_say Kc _ _ (S.Wit × Wp) E 0 (splitNx S St₁ St₂ St₀) (E₀.prod S.ext) _ _ _ ?_
      (fun _ _ _ h => h) (fun _ => rfl) ?_,
    ⟨?_, ?_, ?_, ?_, ?_⟩,
    ?_⟩
  · rintro x y w ⟨hE, hA, hin, hr⟩
    exact ⟨hE, hA,
      (ldSpl_sum E S G₁ G₂ k St₁ St₂ sl₁ sl₂ x.1.1.1 x.1.1.2.1 x.1.1.2.2 (S.msgs w.1)).2 hin, hr⟩
  · rintro x y t w _ ⟨hd, hout, hr⟩
    exact ⟨hd,
      (ldSpl_sum E S G₁ G₂ k St₁ St₂ sl₁ sl₂ x.1.1.1 x.1.1.2.1 x.1.1.2.2 (S.msgs w.1)).1 t hout,
      hr⟩
  · exact ⟨fun p => p.elim (fun q => q.elim) fun q => q.elim⟩
  · intro w x
    exact Set.union_self _
  · intro w x c ρ
    show ((splitVal k sl₁ (S.msgs w.1) x.1.1.2.1, ()) : E × Unit) =
      (splitVal k sl₁ (S.cut Rd (S.msgs w.1)) x.1.1.2.1, ())
    unfold splitVal
    rw [G₁.slf_val_cut Rd sl₁ _ (hr _), hv]
  · intro xp m M h
    show sl₁.val xp.2.1 (G₁.msg (k.put M m)) + sl₂.val xp.2.2 (G₂.msg (k.put M m)) = xp.1
    rw [k.slf_val_put G₁ k.h₁ sl₁ xp.2.1 (h0 _) M m, k.slf_val_put G₂ k.h₂ sl₂ xp.2.2 (h0' _) M m]
    exact h
  · intro m xp ρ _
    have e : (fun M : E => ((splitVal k sl₁ (k.put M m) xp.2.1, ()) : E × Unit)) =
        (fun u : E => ((u, ()) : E × Unit)) ∘ fun M : E => sl₁.val xp.2.1 (G₁.msg m) + M := by
      funext M
      show ((sl₁.val xp.2.1 (G₁.msg (k.put M m)) + k.val (k.put M m), ()) : E × Unit) = _
      rw [k.slf_val_put G₁ k.h₁ sl₁ xp.2.1 (h0 _) M m, k.val_put]
      rfl
    show (unif E).map (fun M : E => ((splitVal k sl₁ (k.put M m) xp.2.1, ()) : E × Unit)) =
      (unif E).map fun u : E => ((u, ()) : E × Unit)
    rw [e, ← PMF.map_comp, map_unif_of_bijective (AddGroup.addLeft_bijective _)]
  · intro x y w h
    show sl₁.val x.1.1.2.1 (G₁.msg (S.cut Rd (S.msgs w.1))) +
        sl₂.val x.1.1.2.2 (G₂.msg (S.cut Rd (S.msgs w.1))) = x.1.1.1
    rw [G₁.slf_val_cut Rd sl₁ _ (hr _), G₂.slf_val_cut Rd sl₂ _ (hr' _)]
    exact h.2.2.1

end Cb
