-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Reads/RowBehind.lean: the row claim_read_same_index at the output head's link, for the
four forms of the policy, at the state behind three yeses of the kind's and the description's own
texts.

What is shown.
  `public_ne`: a tool: at every filling and every state, the part in U3 of the form mean is not the
    zero form.
  `sane_of_close`: where a state lies as Reads/HeadAtRecord.lean asks, the letters are sane, from
    two public premises: every read's name is found in the public table; `NumH`.
  `Public Z`: the public premises of `head_at` (Reads/HeadAtRecord.lean) and of `lies_of_three`
    (Reads/ClaimsAtRecord.lean), in one structure. It names no state.
  `row_behind_three`: **under `Public Z`: behind a yes of the kind's own decision on its rounds, a
    yes of the block of a commitment with the reads' quiet step behind it, and a yes of the kind's
    run "policy" at the state s4 that this leaves: the statement at the head with the clause on the
    weights holds of the letters filled from the state (`HeadClaimW Z.letters`); s4 is one of the
    states of which it speaks; and the claims that the run returns are the letters' four forms at
    s4.** Four premises speak of a state, by name: the ledger in front of the head's own rounds is
    well laid; the reads' array in the ledger of s4 has the public number of columns; the lookup's
    two points on the planes have all their coordinates.

Limits. `row_behind_three` is a lemma on the way: it speaks of no run of the seated description,
where the claims are run later than at the state behind the quiet step: see Reads/RowAtSeat.lean.
The four are shown by nothing here. `Public Z` holds hJ, which is shown of no real layout.

(Where this and lean/THEOREM.md differ, the page holds.) That the
three texts stand one behind the other in the seated description, with these parameters, is not
shown: so nothing is yet said of the description as a whole. From the state's words to an instance
nothing is shown. What is spent of the row is not joined here. Four forms of 35. The full size
alone. Nothing on soundness.


-/
import Johnson.Desc.Reads.ClaimsAtRecord

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Reads.AtSeat

open OnBytes.Model (Reading)
open OnBytes.Model.Head (matsH callNo)
open OnBytes.Road.Hd (NumH)
open VerifiableInference.Desc.First (S HeadOwn)
open VerifiableInference.Desc.K8 (ReadsQuiet.head)
open VerifiableInference.Desc.Kinds
open VerifiableInference.Desc.Kinds.Head
open VerifiableInference.Desc.Kinds.Head.Law
open VerifiableInference.Reads.AtHead

/-- The part in U3 of the form mean is not the zero form. -/
theorem public_ne (Z : Fill) (s : S) :
    u3Value Reading.gl.val Z.seat.iU3 Z.seat.cols (Z.letters.form s .B2)
      (fun p => if p = Z.seat.start .rowCount + (NR + 0) then 1 else 0) ≠ 0 := by
  have e := (u3Value_part (ρ := Reading.gl) Z.seat.iU3 Z.seat.cols
    (fun p => if p = Z.seat.start .rowCount + (NR + 0) then 1 else 0)
    (Z.letters.form s .B2)).trans
    (mean_part (iS := Z.letters.sizes) (iP := Z.letters.policy) (iR := Z.letters.request s)
      Reading.gl Z.seat (fun p => if p = Z.seat.start .rowCount + (NR + 0) then 1 else 0))
  refine ne_of_eq_of_ne e ?_
  rw [bytesAt_ind, bytesAt_ind, bytesAt_ind, if_pos (by decide), if_neg (by decide),
    if_neg (by decide)]
  simp

/-- Where a state lies so, the letters are sane. -/
theorem sane_of_close (Z : Fill) (hfirst : ∀ r, (Z.seat.first r).isSome = true)
    (hN : NumH Z.h Z.L) {s : S} (hs : Z.AtClose s) : Z.letters.Sane :=
  ⟨hfirst, hN,
    ⟨List.cons_ne_nil _ _, fun _ _ => ⟨s, hs, Z.letters.form s .B2, List.mem_cons.2 (Or.inl rfl),
      fun p => if p = Z.seat.start .rowCount + (NR + 0) then 1 else 0, public_ne Z s⟩⟩,
    ⟨Reading.gl, rfl⟩⟩

/-- The public premises. -/
structure Public (Z : Fill) : Prop where
  first : ∀ r, (Z.seat.first r).isSome = true
  num : NumH Z.h Z.L
  tab : Z.tab = planTab Z.h Z.hp.tl.mats
  mats : ∃ gid sid, Z.hp.tl.mats = matsH Z.h Z.L Z.b gid sid
  nm : Z.hp.tl.NM = 8
  la : Z.h.la = 16
  hJ : ∀ q, q < 6 → (Z.L.calls.getD q default).lJ =
    (letI := sizesOf Z.h; lJ (OnBytes.Model.Head.keyFloor Z.h) (callKeys q))
  hlsJ : ∀ q, q < 6 → Z.h.ls ≤ (Z.L.calls.getD q default).lJ
  hc6 : ∀ seg q, callNo Z.L seg = some q → q < 6
  hls : Z.h.ls ≤ (letI := sizesOf Z.h; Norm.lNI + Norm.lPd)
  cols : 0 < Z.cols
  T : (letI := sizesOf Z.h; Norm.T) = Inst.Model.Head.nT
  S2 : (letI := sizesOf Z.h; Norm.S2) = 64
  d : (letI := sizesOf Z.h; Norm.d) = 5120
  JV : (letI := sizesOf Z.h; Head.JV) = 202048
  count : ∀ u : Use, u ∈ (letI := sizesOf Z.h; usesH) →
    (letI := sizesOf Z.h; u.index) < Z.seat.count u.read

/-- **The row at the head, at the state behind three yeses.** -/
theorem row_behind_three {Cl : Type} (cl : Form → Cl) (Z : Fill) (U : Public Z)
    (place : VerifiableInference.Desc.Place) (link4 piece4 : ℕ) {s0 s2 s4 : S}
    {rs4 : List Fmt.RoundView} {gs4 : List (List (ℕ × List UInt64))}
    (h4 : (kind cl (seatAt Z.h Z.iU3) link4 piece4 (parOf Z.h Z.work)).decide s0 rs4 gs4 = .ok s2)
    (P : VerifiableInference.Desc.K1.Par) (link moment : ℕ) (arrays : Option (List ℕ))
    {rs : List Fmt.RoundView} {gs : List (List (ℕ × List UInt64))}
    (h5 : (VerifiableInference.Desc.K8.ReadsQuiet.behind
      (VerifiableInference.Desc.K1.commitAtS P link moment arrays)
      (ReadsQuiet.head ⟨place, Z.h, Z.L, Z.hp⟩)).decide s2 rs gs = .ok s4)
    {c : String × (ℕ → S → Except String (List Cl × S))}
    (hc : c ∈ (kind cl (seatAt Z.h Z.iU3) link4 piece4 (parOf Z.h Z.work)).claims)
    (hname : c.1 = "policy") {n : ℕ} {y : List Cl × S} (hrun : c.2 n s4 = .ok y)
    (hWL : WellLaid ((seatAt Z.h Z.iU3).ledger s0))
    (hcols : ∀ o, s4.here = .head o → ∃ tr, o.F.trees[Z.iU3]? = some tr ∧ tr.K = Z.cols)
    (hzb : ∀ o x, s2.here = .head o → o.x = some x →
      x.g1.zb0.size = x.g1.shape.kT + x.g1.shape.cK + 5 ∧
      x.g1.zb1.size = x.g1.shape.kT + x.g1.shape.cK + 5) :
    HeadClaimW Z.letters ∧ Z.AtClose s4 ∧ y.1 = (Z.letters.letters.forms () s4).map cl := by
  have hs : Z.AtClose s4 := lies_of_three cl Z U.tab place link4 piece4 h4 hWL
    (U.hJ 0 (by decide)) (U.hlsJ 0 (by decide)) P link moment arrays h5 hc hrun hcols hzb
  refine ⟨head_at Z (sane_of_close Z U.first U.num hs) U.mats U.nm U.la U.hJ U.hlsJ U.hc6 U.hls
    U.cols U.T U.S2 U.d U.JV U.count, hs, ?_⟩
  obtain ⟨o, cov, x, t, g, bh, pl, Q⟩ := hs
  exact policy_claims cl Z link4 piece4 Q hc hname hrun

end VerifiableInference.Reads.AtSeat

#print axioms VerifiableInference.Reads.AtSeat.public_ne
#print axioms VerifiableInference.Reads.AtSeat.sane_of_close
#print axioms VerifiableInference.Reads.AtSeat.row_behind_three
