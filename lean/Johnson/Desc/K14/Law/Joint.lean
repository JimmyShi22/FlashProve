-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Law/Joint.lean: what the state that the linear claim's shared rounds hand to the
two proximity tests means: if all constraints on the two groups hold of words, then the three
families' equations hold of these words.

Main names: Later (a group's list of constraints has only grown at its end), recSays, locSays,
foldSays, ratio_of_count (a count that is at most k q ^ (k - 1) is, times q, at most k q ^ k).

What is not claimed. That the constraints hold of words is the proximity tests' law's to give. That
a group's list only grows between a place and the tests is asked as a premise (Later). Nothing on
the three equations pinning the folded row to the encoded index. Nothing on soundness of a verifier.

-/
import Johnson.Desc.K14.Law.Step
import Johnson.Desc.K14.Law.LaysRL

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params Desc.Plain
open OnBytes.Model (Reading)
open OnBytes.Means (Words)
open VerifiableInference.Desc.Ground (ok)

variable {K : Type} [Field K] (ρ : Reading K)

/-- The group's list of constraints at e is that at d with more at its end. -/
def Later (d e : St) (g : Nat) : Prop := ∃ more, rowsOn e g = rowsOn d g ++ more

/-- A list made item by item: each item's own is in it. -/
theorem mem_mapM {α β : Type} (f : α → Option β) : ∀ (l : List α) (r : List β),
    l.mapM f = some r → ∀ a ∈ l, ∃ b ∈ r, f a = some b := by
  intro l
  induction l with
  | nil => intro r _ a ha; cases ha
  | cons x l ih =>
    intro r h a ha
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨b, hb, bs, hbs, rfl⟩ := h
    rcases List.mem_cons.1 ha with rfl | ha
    · exact ⟨b, List.mem_cons_self, hb⟩
    · obtain ⟨c, hc, hfc⟩ := ih bs hbs a ha
      exact ⟨c, List.mem_cons_of_mem _ hc, hfc⟩

/-- **What (rec_gamma)'s constraints mean at the tests.** -/
theorem recSays (p : Par) (d d' e : St) (rs : List Fmt.RoundView) (T : Statement) (m : Words K)
    (h : laysRec p d rs = some d') (hl : Later d' e d.loc.gU)
    (hs : Means.AllSay ρ T (rowsOn e d.loc.gU) m) (hi : p.S.fold.index.ok = true)
    (hP : PlacedU T p.S.fold d.loc.oU) :
    ∀ x ∈ d.loc.key.seeds.zipIdx,
      RecEq p.S.fold.index (x.1.z.map ρ.val) (ρ.val x.1.beta) (fun t => ρ.val (thetaE t)) x.2
        (fun r => ρ.val ((weights p.S d.loc).getD r zeroE))
        (fun k => ρ.val (d.loc.key.record.getD k zeroE))
        (fun k => m d.loc.oU.oracle .main (d.loc.oU.lay.index k)) := by
  intro x hx
  obtain ⟨hok, _, rows, hrows, hU, _⟩ := laysRecW p d d' rs h
  obtain ⟨more, hmore⟩ := hl
  obtain ⟨row, hrow, hg⟩ := mem_mapM _ _ _ hrows x hx
  have hsay : Means.Says ρ T row m := hs row (by rw [hmore, hU]; simp [hrow])
  simp only [ok, laysRecL, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at hok
  have hfit : d.loc.key.fits p.S.fold.index = true := hok.1
  simp only [TableKey.fits, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hfit
  have hx' : d.loc.key.seeds[x.2]? = some x.1 := List.mem_zipIdx_iff_getElem?.1 hx
  have hlt : x.2 < p.S.fold.index.answers := by
    rw [← hfit.1.2]
    exact (List.getElem?_eq_some_iff.1 hx').1
  have hz : x.1.z.length = p.S.fold.index.cubeBits := hfit.2 _ (List.mem_of_getElem? hx')
  exact (recMeansW ρ T p.S.fold x.1 x.2 _ _ _ row hi hlt hz hg hP m).1 hsay

/-- **What (loc_x)'s constraints mean at the tests.** -/
theorem locSays (p : Par) (d d' e : St) (r : Fmt.RoundView) (cols : List (Nat × List UInt64))
    (T : Statement) (m : Words K) (h : loc p d [r] [cols] = some d') (hl : Later d' e d.loc.gU)
    (hs : Means.AllSay ρ T (rowsOn e d.loc.gU) m) (hi : p.S.fold.index.ok = true)
    (hP : PlacedU T p.S.fold d.loc.oU) :
    ∀ x ∈ locations p r, ∃ col, cols.lookup x = some col ∧
      LocEq ρ p.S.fold (generatorAt p.S.fold.index.code x)
        (fun r => ρ.val ((weights p.S d.loc).getD r zeroE)) (weights p.S d.loc).size
        (fun r => ρ.val (ofF (col.toArray.getD r 0)))
        (fun k => m d.loc.oU.oracle .main (d.loc.oU.lay.index k)) := by
  intro x hx
  obtain ⟨_, rows, hrows, _, hU, _⟩ := laysLocW p d d' r cols h
  obtain ⟨more, hmore⟩ := hl
  obtain ⟨row, hrow, hg⟩ := mem_mapM _ _ _ hrows x hx
  have hsay : Means.Says ρ T row m := hs row (by rw [hmore, hU]; simp [hrow])
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at hg
  obtain ⟨col, hcol, hg⟩ := hg
  exact ⟨col, hcol, (locMeansW ρ T p.S.fold x _ _ _ row hi hg hP m).1 hsay⟩

/-- **What (fold)'s two constraints mean at the tests.** -/
theorem foldSays (p : Par) (d d' e : St) (r : Fmt.RoundView) (T : Statement) (m : Words K)
    (hS : p.S.sharedSplitNeeded = true) (h : split p d [r] = some d')
    (hlO : Later d' e d.loc.gOmega) (hlU : Later d' e d.loc.gU)
    (hsO : Means.AllSay ρ T (rowsOn e d.loc.gOmega) m)
    (hsU : Means.AllSay ρ T (rowsOn e d.loc.gU) m)
    (hP : Placed T p.S d.loc (linLayOmega d.st.codes p.S)) :
    FoldEq p.S ((d.loc.psiSh.take p.S.kLo).map ρ.val) (d.loc.zFd.map ρ.val)
      (omegaOf d.loc (linLayOmega d.st.codes p.S) m) (uOf d.loc m) := by
  obtain ⟨row, a, b, hf, h1, h2, h3⟩ := laysW ρ p d d' r hS h
  obtain ⟨mO, hmO⟩ := hlO
  obtain ⟨mU, hmU⟩ := hlU
  have ha : Means.Says ρ T a m := hsO a (by rw [hmO, h1]; simp)
  have hb : Means.Says ρ T b m := hsU b (by rw [hmU, h2]; simp)
  exact (foldMeansW ρ T p.S d.loc _ row hf hP m).1 (h3 T m ha hb)

/-- A count that is at most k q ^ (k - 1) is, times q, at most k q ^ k. -/
theorem ratio_of_count (c k q : Nat) (h : c ≤ k * q ^ (k - 1)) : c * q ≤ k * q ^ k := by
  cases k with
  | zero => simp at h; simp [h]
  | succ k =>
    rw [Nat.add_sub_cancel] at h
    calc c * q ≤ (k + 1) * q ^ k * q := Nat.mul_le_mul_right _ h
      _ = (k + 1) * q ^ (k + 1) := by ring

end Desc.K14.Law
