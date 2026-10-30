-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Sound/RuleErrProofs.lean: the proofs of the statements of
Johnson/Desc/Sound/RuleErr.lean. Theorems and the lemmas that they need.

Limits: those of that file.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.RuleErr
import Johnson.Desc.Sound.GoodInProofs
import Prob.Count

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker OnBytes.Flat KObj
open OnBytes (E)
open TypedOracleCompiler.Run.PQ (uL rvSL RD)
open _root_.Run.PQ (CK SgX PlainOf)
open _root_.Iop (Reduction Err Shape IOR ExtSpec oneExternalString Doomed)
open _root_.Prob (cnt cnt_mono)
open VerifiableInference.Desc.First.Prod (Enc trL famL errL BoundL famL_clean famL_within
  cnt_mem_le)

theorem readIsView : ReadIsView := by
  intro C ds
  induction ds with
  | nil => exact fun _ => rfl
  | cons d ds ih =>
    rintro ⟨m, c, τ⟩
    show _ :: trL (encRV C ds) τ = _ :: rvSL C ds τ
    rw [ih τ]

theorem cleanIsNoBad : CleanIsNoBad := by
  intro C bad ds h τ
  rw [famL_clean, readIsView]
  constructor
  · intro H i r hi j x hx hb
    exact H i r hi ⟨j, x, hx, hb⟩
  · rintro H i r hi ⟨j, x, hx, hb⟩
    exact H i r hi j x hx hb

theorem strikeLast_concat (l : List Fmt.RoundView) (y : Fmt.RoundView) :
    strikeLast (l ++ [y]) = l ++ [cutTo y 0] := by
  simp [strikeLast]

theorem struckIsCase : StruckIsCase := by
  intro bad t
  constructor
  · intro H i r hi j x hx
    have k := H i r hi x (List.mem_of_getElem? hx)
    show E.ofTriple x ∉ bad (strikeLast ([] ++ t.take i ++ [cutTo r j]))
    rw [strikeLast_concat]
    simpa [cutTo] using k
  · intro H i r hi x hx
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hx
    have k : E.ofTriple x ∉ bad (strikeLast ([] ++ t.take i ++ [cutTo r j])) := H i r hi j x hj
    rw [strikeLast_concat] at k
    simpa [cutTo] using k

theorem oneToOne : OneToOne := by
  classical
  intro C d val h1 hinj
  refine ⟨fun c => by simp [h1 c], fun j n L hL => ?_⟩
  cases j with
  | zero =>
    have a : cnt (fun c => ∃ x, (elemsAt C d c)[0]? = some x ∧
        E.ofTriple x ∈ L ((elemsAt C d c).take 0)) ≤
        cnt (fun c => E.ofTriple (val c) ∈ (L []).toFinset) := by
      refine cnt_mono fun c => ?_
      rintro ⟨x, hx, hb⟩
      rw [h1 c] at hx hb
      have e : val c = x := by simpa using hx
      subst e
      simpa using hb
    refine le_trans a (le_trans (cnt_mem_le _ hinj _) ?_)
    simpa using le_trans (List.toFinset_card_le _) (hL [])
  | succ j =>
    have a : cnt (fun c => ∃ x, (elemsAt C d c)[j + 1]? = some x ∧
        E.ofTriple x ∈ L ((elemsAt C d c).take (j + 1))) ≤ cnt (fun _ : Iop.GChal d.entry.work
          (C.Ch d.entry d.kind) => False) := by
      refine cnt_mono fun c => ?_
      rintro ⟨x, hx, _⟩
      rw [h1 c] at hx
      simp at hx
    refine le_trans a ?_
    simp [cnt]

theorem ruleBound : RuleBound := by
  classical
  intro C bad ceil k f ds
  induction ds with
  | nil => exact fun _ _ _ => trivial
  | cons d ds ih =>
    intro n hc hm
    refine ⟨fun pre m hpre => ?_, ih (n + 1) hc fun j d' hj => ?_⟩
    · obtain ⟨hk, hf⟩ := hm 0 d rfl
      haveI : Fintype (Iop.GChal d.entry.work (C.Ch d.entry d.kind)) := Fintype.ofFinite _
      let L : List Fmt.Ext → List E := fun q =>
        bad (pre ++ [⟨PlainOf.gots d.items (Iop.GPlain.old (b := d.entry.work) m.2),
          ⟨q, [], [], none⟩⟩])
      have hL : ∀ q, (L q).length ≤ ceil n := fun q => by
        have l := hc (pre ++ [⟨PlainOf.gots d.items (Iop.GPlain.old (b := d.entry.work) m.2),
          ⟨q, [], [], none⟩⟩])
        simpa [hpre] using l
      let P : Fin (k (n + 0)) → Iop.GChal d.entry.work (C.Ch d.entry d.kind) → Prop := fun j c =>
        ∃ x, (elemsAt C d c)[j.1]? = some x ∧ E.ofTriple x ∈ L ((elemsAt C d c).take j.1)
      have h1 : cnt (fun c => ∃ j, P j c) ≤
          Fintype.card (Fin (k (n + 0))) * (ceil n * f (n + 0)) :=
        Prob.cnt_exists_le_mul P _ fun j => hf j.1 (ceil n) L hL
      have h2 : cnt (fun c : Iop.GChal d.entry.work (C.Ch d.entry d.kind) =>
          judgeOf bad pre ⟨PlainOf.gots d.items (Iop.GPlain.old (b := d.entry.work) m.2),
            C.dr d.entry d.kind (Iop.GChal.old (b := d.entry.work) c)⟩) ≤
          cnt (fun c => ∃ j, P j c) := by
        refine cnt_mono fun c => ?_
        rintro ⟨j, x, hx, hb⟩
        have hj : j < k (n + 0) :=
          lt_of_lt_of_le (List.getElem?_eq_some_iff.1 hx).1 (hk c)
        exact ⟨⟨j, hj⟩, x, hx, hb⟩
      refine le_trans h2 (le_trans h1 ?_)
      simp
    · have q := hm (j + 1) d' (by simpa using hj)
      rwa [show n + (j + 1) = n + 1 + j by omega] at q

theorem within_bears (C : CK) (need : ℕ → ℕ) :
    ∀ (ds : List RD) (n : ℕ) (B : Iop.BadFam (uL C ds)) (ε : Err (uL C ds)),
      B.Within (errL need (uL C ds) n) → ErrBears C need ds n ε → B.Within ε
  | [], _, _, _, _, _ => trivial
  | _ :: ds, n, (_, kk), (_, ε), hw, hb =>
    ⟨fun m => le_trans (hw.1 m) hb.1,
      fun m c => within_bears C need ds (n + 1) (kk m c) ε (hw.2 m c) hb.2⟩

theorem ruleWithin : RuleWithin := fun C bad ceil k f ds h ε hc hm hb =>
  within_bears C _ ds h.length _ ε
    (famL_within _ _ _ _ h (ruleBound C bad ceil k f ds h.length hc hm)) hb

theorem goodInOfRule : GoodInOfRule := by
  intro S Cl W C F p on on' R R' bad ceil k f hc hm hb h1 h2
  refine goodInOfBadFam S Cl W C F p on on' R R'
    (fun a => famL (judgeOf (bad a)) (uL C (toRDs p.ds)) (encRV C (toRDs p.ds)) []) ?_ ?_ ?_
  · intro a ha
    exact ruleWithin C _ ceil k f (toRDs p.ds) [] p.err (fun g => hc a g ha)
      (fun j d hj => by simpa using hm j d hj) hb
  · intro a τ b ha hcl hout
    exact h1 a τ b ha ((cleanIsNoBad C _ (toRDs p.ds) [] τ).1 hcl) hout
  · intro a τ b w ha hcl hout hw
    exact h2 a τ b w ha ((cleanIsNoBad C _ (toRDs p.ds) [] τ).1 hcl) hout hw

theorem doomedOfRule : DoomedOfRule := by
  intro S Cl W C F p on Q bad ceil k f hc hm hb h1 a ha
  refine Iop.doomed_of_clean _ p.err
    (famL (judgeOf (bad a)) (uL C (toRDs p.ds)) (encRV C (toRDs p.ds)) []) _ ?_ ?_
  · exact ruleWithin C _ ceil k f (toRDs p.ds) [] p.err (fun g => hc a g ha)
      (fun j d hj => by simpa using hm j d hj) hb
  · intro τ hcl b hout
    exact h1 a τ b ha ((cleanIsNoBad C _ (toRDs p.ds) [] τ).1 hcl) hout

end VerifiableInference.Desc.Sound
