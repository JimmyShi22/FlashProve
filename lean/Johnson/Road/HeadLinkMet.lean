-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/HeadLinkMet.lean: most hypotheses of the theorem on the output head's link can be met
together.

The theorem head_link_of_port (Johnson/Road/HeadLinkPort.lean) goes from routines of the verifier
that succeed, and from what the protocol's random steps are meant to give, to "the reply is the
model's first choice". What the random steps are meant to give is a bundle of hypotheses on
integer matrices Mz, a world W and functions fn on the calls' columns. This file shows that most
of the bundle can be met together: for a true request for the next token and a run of the
verifier's routines on it there are Mz, W and fn that meet all of it but the lookup's own claims
(see "What is not witnessed").

How.
 1. matsFrom: integer matrices that hold given cells where the verifier's rule reads them, and 0
    elsewhere. At the library's sizes the cells read in them are the given cells at every name that
    the head reads (sameZ_matsFrom); if the cells are small, all entries are (matsFrom_small).
 2. The cells are the library's honest cells of the head with the cost ledger, at the policy 0, 0,
    0. There every key of all nine families is a row of its table and the 17 identities are 0. So
    the conclusions of the two steps from one point to all indices hold (lookup_met, idns_same),
    and with them the steps, which are implications.
 3. slotsFor: values for the slots. The slots of the sums of limb products, of the row products and
    the first slots of two sumchecks get what they are meant to hold. The routine hear takes these
    slots in a fixed order, so they are different slots (slotOrder_of_hear, over
    Johnson/Road/HeadSlots.lean). Two more slots, which the hidden value at the end of the lookup's
    key side reads, are chosen so that the claim on the calls' key vectors holds (solve_two).
 4. A world with these slots in which every table holds what it says of the matrices exists
    (holdsH_met in Johnson/Road/HeadMet.lean). In it the 17 claims of the ledger are worth the
    extensions of identities that are 0.

Main definitions: matsFrom, slotsFor, SlotOrder, joinRest, LinkWorld (the bundle).
Main theorems: sameZ_matsFrom, same_matsFrom, matsFrom_small, layersGive_matsFrom; rows_kvOf,
idns_same, isLut_at, lookup_met; slotOrder_of_hear; link_met_end, link_met; LinkWorld.fits (the
fields of the bundle are head_link_of_port's hypotheses letter by letter); seg_met (the same
bundle with the hypothesis LentH of head_link_seg, Johnson/Road/HeadLinkSeg.lean, met by choice);
true_exists_ref.

What stays a hypothesis in link_met. The public side and "the routines succeed", as in
head_link_of_port: layout, planH2, hear on a view and tablesOf return; nine numbers of the shape,
sh = 8, F = 24, sT = 4; the record of the stream's matrix; the request of the run is the
instance's (ReqFits); the final normalisation's numbers are lawful. And that the request is a true
one under the policy 0, 0, 0 (RinfR). true_exists_ref: such a request exists at the final
normalisation 44, 30, 53,687; that these are the numbers of the full-size example's shape is held
by a run (Johnson/Road/HeadRunK.lean). The shape of the hidden value at the end of the lookup's
key side, which step 3 uses, is a theorem of Johnson/Road/HeadEndForm.lean.

What is not witnessed here. The hypothesis ClaimsHold of head_link_of_port has four clauses. The
bundle LinkWorld has the first two: the 17 claims of the ledger and the claim on the calls' key
vectors. It lacks the other two: the lookup's claims that read mask entries alone (the tie's, one
for each level of the two product trees, the bits'), and its three claims on the planes of the
counts. The matrix of the counts is 0 in matsFrom, so the third claim on the planes, that the
counts add up to the number of keys, does not hold in this file's world.
Johnson/Road/HeadLookMet.lean meets all four clauses, in another world, with this file's tools
(link_met_all, seg_met_all).

What is not claimed. The world is made for the matrices: it is not the world of a prover's
messages, and the claims of the sub-proof other than the 18 are not looked at. That the walk
succeeds is a hypothesis of LinkWorld.fits alone. Nothing on what a verifier's acceptance shows.
The program does not import this file.
-/
import Johnson.Road.HeadLinkSeg
import Johnson.Road.HeadMet
import Johnson.Road.HeadSlots
import Johnson.Road.HeadEndForm
import Policy.Seg.HeadAsm
import Cm.Rel2Guards

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.Hd

open Finset
open Inst.Model Inst.Model.Head
open OnBytes.Model (Reading World Aff Fork SubM Row5)

/-! ## 1. Matrices that hold given cells -/

/-- Integer matrices, in the order of the list of the head's sub-proof at the library's sizes, that
hold the cells tz where the verifier's rule reads them: the four parts of hf, then hd, hr, nothing
for the matrix of the lookup's counts, and the stream. An entry at which no cell is read is 0. -/
def matsFrom (tz : Head.Cells ℤ) (a r c : ℕ) : ℤ :=
  if a < 4 then
    if c < 4816 ∧ r < 65536 ∧ (a * 4816 + c) * 64 + r / 1024 < 1232768 then
      tz.hf ((a * 4816 + c) * 64 + r / 1024) (r % 1024)
    else 0
  else if a = 4 then
    if c < 640 ∧ r < 16384 then tz.hd (c * 16 + r / 1024) (r % 1024) else 0
  else if a = 5 then
    if c < 15 ∧ r < 8192 then tz.hr (c * 8 + r / 1024) (r % 1024) else 0
  else if a = 7 then
    if c < 400 ∧ r < 65536 then tz.x (c * 64 + r / 1024) (r % 1024) else 0
  else 0

/-- At the place where the rule reads cell (φ, i) of hf, the matrices hold that cell. -/
theorem matsFrom_at_hf (tz : Head.Cells ℤ) {φ i : ℕ} (hφ : φ < 1232768) (hi : i < 1024) :
    matsFrom tz (0 + φ / 64 / 4816) (φ % 64 * 1024 + i) (φ / 64 % 4816) = tz.hf φ i := by
  have e1 : 0 + φ / 64 / 4816 < 4 := by omega
  have e2 : φ / 64 % 4816 < 4816 ∧ φ % 64 * 1024 + i < 65536 ∧
      ((0 + φ / 64 / 4816) * 4816 + φ / 64 % 4816) * 64 + (φ % 64 * 1024 + i) / 1024 < 1232768 :=
    ⟨by omega, by omega, by omega⟩
  have e3 : ((0 + φ / 64 / 4816) * 4816 + φ / 64 % 4816) * 64 + (φ % 64 * 1024 + i) / 1024 = φ := by
    omega
  have e4 : (φ % 64 * 1024 + i) % 1024 = i := by omega
  unfold matsFrom
  rw [if_pos e1, if_pos e2, e3, e4]

/-- The same for hd. -/
theorem matsFrom_at_hd (tz : Head.Cells ℤ) {φ i : ℕ} (hφ : φ < 10240) (hi : i < 1024) :
    matsFrom tz (4 + φ / 16 / 640) (φ % 16 * 1024 + i) (φ / 16 % 640) = tz.hd φ i := by
  have n1 : ¬ 4 + φ / 16 / 640 < 4 := by omega
  have e1 : 4 + φ / 16 / 640 = 4 := by omega
  have e2 : φ / 16 % 640 < 640 ∧ φ % 16 * 1024 + i < 16384 := ⟨by omega, by omega⟩
  have e3 : φ / 16 % 640 * 16 + (φ % 16 * 1024 + i) / 1024 = φ := by omega
  have e4 : (φ % 16 * 1024 + i) % 1024 = i := by omega
  unfold matsFrom
  rw [if_neg n1, if_pos e1, if_pos e2, e3, e4]

/-- The same for hr. -/
theorem matsFrom_at_hr (tz : Head.Cells ℤ) {φ i : ℕ} (hφ : φ < 120) (hi : i < 1024) :
    matsFrom tz (4 + 1 + φ / 8 / 15) (φ % 8 * 1024 + i) (φ / 8 % 15) = tz.hr φ i := by
  have n1 : ¬ 4 + 1 + φ / 8 / 15 < 4 := by omega
  have n2 : ¬ 4 + 1 + φ / 8 / 15 = 4 := by omega
  have e1 : 4 + 1 + φ / 8 / 15 = 5 := by omega
  have e2 : φ / 8 % 15 < 15 ∧ φ % 8 * 1024 + i < 8192 := ⟨by omega, by omega⟩
  have e3 : φ / 8 % 15 * 8 + (φ % 8 * 1024 + i) / 1024 = φ := by omega
  have e4 : (φ % 8 * 1024 + i) % 1024 = i := by omega
  unfold matsFrom
  rw [if_neg n1, if_neg n2, if_pos e1, if_pos e2, e3, e4]

/-- The same for the head's copy of the stream. -/
theorem matsFrom_at_x (tz : Head.Cells ℤ) {φ i : ℕ} (hφ : φ < 25600) (hi : i < 1024) :
    matsFrom tz (4 + 3 + φ / 64 / 400) (φ % 64 * 1024 + i) (φ / 64 % 400) = tz.x φ i := by
  have n1 : ¬ 4 + 3 + φ / 64 / 400 < 4 := by omega
  have n2 : ¬ 4 + 3 + φ / 64 / 400 = 4 := by omega
  have n3 : ¬ 4 + 3 + φ / 64 / 400 = 5 := by omega
  have e1 : 4 + 3 + φ / 64 / 400 = 7 := by omega
  have e2 : φ / 64 % 400 < 400 ∧ φ % 64 * 1024 + i < 65536 := ⟨by omega, by omega⟩
  have e3 : φ / 64 % 400 * 64 + (φ % 64 * 1024 + i) / 1024 = φ := by omega
  have e4 : (φ % 64 * 1024 + i) % 1024 = i := by omega
  unfold matsFrom
  rw [if_neg n1, if_neg n2, if_neg n3, if_pos e1, if_pos e2, e3, e4]

/-- If the cells are small, every entry of the matrices is small. -/
theorem matsFrom_small {tz : Head.Cells ℤ} (hS : Head.Small tz) (a r c : ℕ) :
    |matsFrom tz a r c| < 2 ^ 18 := by
  have hp : r % 1024 < nT := Nat.mod_lt _ (by norm_num)
  have h0 : |(0 : ℤ)| < 2 ^ 18 := by norm_num
  unfold matsFrom
  by_cases h1 : a < 4
  · rw [if_pos h1]
    by_cases h2 : c < 4816 ∧ r < 65536 ∧ (a * 4816 + c) * 64 + r / 1024 < 1232768
    · rw [if_pos h2]
      exact (hS _ hp).1 _ h2.2.2
    · rw [if_neg h2]
      exact h0
  · rw [if_neg h1]
    by_cases h3 : a = 4
    · rw [if_pos h3]
      by_cases h4 : c < 640 ∧ r < 16384
      · rw [if_pos h4]
        obtain ⟨k1, k2⟩ := h4
        exact (hS _ hp).2.1 _ (by show c * 16 + r / 1024 < 10240; omega)
      · rw [if_neg h4]
        exact h0
    · rw [if_neg h3]
      by_cases h5 : a = 5
      · rw [if_pos h5]
        by_cases h6 : c < 15 ∧ r < 8192
        · rw [if_pos h6]
          obtain ⟨k1, k2⟩ := h6
          exact (hS _ hp).2.2.1 _ (by show c * 8 + r / 1024 < 120; omega)
        · rw [if_neg h6]
          exact h0
      · rw [if_neg h5]
        by_cases h7 : a = 7
        · rw [if_pos h7]
          by_cases h8 : c < 400 ∧ r < 65536
          · rw [if_pos h8]
            obtain ⟨k1, k2⟩ := h8
            exact (hS _ hp).2.2.2 _ (by show c * 64 + r / 1024 < 25600; omega)
          · rw [if_neg h8]
            exact h0
        · rw [if_neg h7]
          exact h0

section Cells

variable {h : Model.Head.Shape} {L : Model.Head.HL} {b : Model.Head.Border}

/-- At the library's sizes the cells that the verifier's rule reads in these matrices are the cells
tz, at every name that the head with the cost ledger reads. -/
theorem sameZ_matsFrom (N : NumH h L) (Bd : BorderH b) (tz : Head.Cells ℤ) :
    Policy.SameMain (cellsH h L b (matsFrom tz)) tz where
  hf := fun φ hφ i hi => by
    show cellIn (matsFrom tz) 0 L.k (L.m / h.T) h.T φ i = tz.hf φ i
    rw [N.k, N.fc, N.T]
    exact matsFrom_at_hf tz hφ hi
  hd := fun φ hφ i hi => by
    show cellIn (matsFrom tz) h.NHf L.kD (L.mD / h.T) h.T φ i = tz.hd φ i
    rw [N.NHf, N.kD, N.fcD, N.T]
    exact matsFrom_at_hd tz hφ hi
  hr := fun φ hφ i hi => by
    show cellIn (matsFrom tz) (h.NHf + 1) L.kR (L.mR / h.T) h.T φ i = tz.hr φ i
    rw [N.NHf, N.kR, N.fcR, N.T]
    exact matsFrom_at_hr tz hφ hi
  x := fun φ hφ i hi => by
    show cellIn (matsFrom tz) (h.NHf + 3) b.kxb (b.mxb / h.T) h.T (b.cell (φ / h.d) (φ % h.d)) i =
      tz.x φ i
    rw [N.NHf, Bd.kxb, N.T, Bd.fc, N.d, Bd.cell]
    have e : fX (φ / 5120) (φ % 5120) = φ := by
      show 5120 * (φ / 5120) + φ % 5120 = φ
      exact Nat.div_add_mod φ 5120
    rw [e]
    exact matsFrom_at_x tz hφ hi

/-- The same with cells and entries read in a ring. -/
theorem same_matsFrom {K : Type} [CommRing K] (N : NumH h L) (Bd : BorderH b) (tz : Head.Cells ℤ) :
    Policy.SameMain (cellsH h L b fun a r c => ((matsFrom tz a r c : ℤ) : K)) (tz.cast K) :=
  have S := sameZ_matsFrom N Bd tz
  ⟨fun φ hφ i hi => congrArg (fun z : ℤ => (z : K)) (S.hf φ hφ i hi),
    fun φ hφ i hi => congrArg (fun z : ℤ => (z : K)) (S.hd φ hφ i hi),
    fun φ hφ i hi => congrArg (fun z : ℤ => (z : K)) (S.hr φ hφ i hi),
    fun φ hφ i hi => congrArg (fun z : ℤ => (z : K)) (S.x φ hφ i hi)⟩

/-- What the layers give at the cells tz they give at the cells read in the matrices. -/
theorem layersGive_matsFrom (N : NumH h L) (Bd : BorderH b) {tz : Head.Cells ℤ}
    {κ : ℕ → LayerScale} {tbs : ℕ → Tables} {w : Weights} {prompt : Fin ppref.T → Fin ppref.V}
    (hl : Top.LayersGive κ tbs w prompt tz) :
    Top.LayersGive κ tbs w prompt (cellsH h L b (matsFrom tz)) where
  ok := hl.ok
  stream := fun a ha j hj => by
    rw [Cm.Seg.xv_same (sameZ_matsFrom N Bd tz).plain hj ha]
    exact hl.stream a ha j hj

end Cells

/-! ## 2. The keys are rows and the identities are 0 at these cells -/

/-- The two functions that name a family's segment agree. -/
theorem nameH_eq (s : Head.Fam) : nameH s = nameOf s := by cases s <;> rfl

/-- The table of a family's kind is the library's table of the family, for every family but HD0.
-/
theorem lutOf_famKind {s : Head.Fam} (hs : s ≠ .HD0) :
    lutOfKind (famKind s) = Policy.LedgerHead.tableOf s := by
  cases s
  case HD0 => exact absurd rfl hs
  all_goals simp [famKind, lutOfKind, Policy.LedgerHead.tableOf]

section Rows

variable {K : Type} [Field K]

/-- Every key under a family's name, as the verifier looks it up, at cells t' that agree with the
integer cells tz where the head reads: it is a row of the library's table for the family's kind,
given the field relation of the head with the cost ledger at tz. -/
theorem rows_kvOf {c : K} (hc : c * 2 ^ 23 = 1) {np : NormPar} {tz : Head.Cells ℤ}
    {t' : Head.Cells K} (Sm : Policy.SameMain t' (tz.cast K)) {H : ℕ → ℕ → K} {y : Req}
    (hL : Policy.LedgerHead.RF (F := K) np H y tz) (s : Head.Fam) {a i : ℕ}
    (ha : a < Head.len s) (hi : i < nT) :
    InLut (lutOfKind (famKind s)) (kvOf c HeadSizes.ref np t' H y (nameOf s) a i) := by
  by_cases hs : s = .HD0
  · subst hs
    have e : kvOf c HeadSizes.ref np t' H y (nameOf .HD0) a i =
        c * Policy.LedgerHead.key np t' H y .HD0 a i :=
      congrFun (congrFun (kv_ref_HD0 c np t' H y) a) i
    rw [e, Policy.keyM_same Sm np H y .HD0 ha hi]
    show InLut (lutOfKind "R16") _
    rw [lut_R16]
    exact (Down.hd0_ledger hc np (tz.cast K) H y a i).1 (hL.keys .HD0 a i ha hi)
  · rw [kv_ref c np t' H y hs, Policy.keyM_same Sm np H y s ha hi, lutOf_famKind hs]
    exact hL.keys s a i ha hi

/-- The identities are 0 at such cells. -/
theorem idns_same {np : NormPar} {tz : Head.Cells ℤ} {t' : Head.Cells K}
    (Sm : Policy.SameMain t' (tz.cast K)) {H : ℕ → ℕ → K} {y : Req}
    (hL : Policy.LedgerHead.RF (F := K) np H y tz) :
    ∀ a < nT, ∀ k < 17, Cm.Plain.idn np t' a k = 0 := by
  intro a ha k hk
  rw [Cm.Seg.idn_same Sm.plain np ha hk]
  exact hL.idns a ha k hk

end Rows

/-- In a layout that the verifier's function returns, at F = 24, sh = 8, sT = 4, the record of call
number q has the library's table for the kind of that call. -/
theorem isLut_at {R : Model.Head.Run} (hy : Model.Head.layout R.h tauFCw = .ok R.L)
    (hF : R.h.famF = 24) (hs : R.h.digSh = 8) (hT : R.h.tabS = 4) {q : ℕ}
    (hq : q < R.L.calls.size) : IsLut (R.L.cl.getD q default) (tabL R q) := by
  have hq' : q < R.L.cl.size := by
    rw [(clN_of_layout hy).1]
    exact hq
  have e1 : R.L.cl[q]? = some (R.L.cl.getD q default) := by
    simp [Array.getD, hq']
  obtain ⟨cd, hcd, _, hl⟩ := isLut_of_layout hy hF hs hT e1
  have e2 : R.L.calls.getD q default = cd := by
    have e3 : R.L.calls[q]? = some (R.L.calls.getD q default) := by
      simp [Array.getD, hq]
    rw [e3] at hcd
    exact Option.some.inj hcd
  unfold tabL
  rw [e2]
  exact hl

/-- **The conclusion of the lookup's step holds at such cells**: every value of each call's function
is the reading of a row of the verifier's table of that call. -/
theorem lookup_met {K : Type} [Field K] {ρ : Reading K} (hρ : Numerals ρ) {R : Model.Head.Run}
    (hy : Model.Head.layout R.h tauFCw = .ok R.L) (hF : R.h.famF = 24) (hs : R.h.digSh = 8)
    (hT : R.h.tabS = 4) (S : SegsFit R) {c : K} (hc : c * 2 ^ 23 = 1) {np : NormPar}
    {tz : Head.Cells ℤ} {t' : Head.Cells K} (Sm : Policy.SameMain t' (tz.cast K))
    {H : ℕ → ℕ → K} {y : Req} (hL : Policy.LedgerHead.RF (F := K) np H y tz)
    {w : ℕ → Array ℕ} {fn : ℕ → ℕ → ℕ → K}
    (hw : ∀ q, (R.L.calls.getD q default).segs.foldlM
      (fun w g => Model.Head.markColumns R w g)
      (Array.replicate (R.L.calls.getD q default).J 0) = some (w q))
    (Kf : ∀ q, KeyFn (R.L.calls.getD q default).segs (w q) (R.L.calls.getD q default).J
      (kvOf c HeadSizes.ref np t' H y)
      (ρ.val (ofF ((R.L.cl.getD q default).tauAt (R.L.cl.getD q default).t0))) (fn q)) :
    ∀ q j, j < (R.L.calls.getD q default).J → ∀ a, a < nT →
      ∃ u, u < 2 ^ (R.L.cl.getD q default).k ∧
        fn q j a = ρ.val (ofF ((R.L.cl.getD q default).tauAt u)) := by
  intro q j hj
  have hq : q < R.L.calls.size := by
    by_contra hn
    have e : R.L.calls.getD q default = default := by
      simp [Array.getD, hn]
    rw [e, default_J] at hj
    exact absurd hj (Nat.not_lt_zero j)
  have hl := isLut_at hy hF hs hT hq
  refine rows_of_keys (hw q) (Kf q)
    (fun v => ∃ u, u < 2 ^ (R.L.cl.getD q default).k ∧
      v = ρ.val (ofF ((R.L.cl.getD q default).tauAt u))) nT ?_ ?_ j hj
  · refine hl.of_inLut hρ ?_
    rw [hl.pad_value hρ]
    exact pad_inLut _
  · intro g hg a ha i hi
    obtain ⟨s, hname, hn, hk⟩ := S q g hg
    refine hl.of_inLut hρ ?_
    unfold tabL
    rw [hk, hname, nameH_eq]
    exact rows_kvOf hc Sm hL s (lt_of_lt_of_le ha hn) hi

/-! ## 3. Values for the slots -/

/-- The cells read in integer matrices, in the challenge field. -/
abbrev cellsE (R : Model.Head.Run) (Mz : Mats ℤ) : Head.Cells Cb.Gl.E :=
  cellsH R.h R.L R.b fun a r c => ((Mz a r c : ℤ) : Cb.Gl.E)

/-- The output matrix of an index, in the challenge field. -/
abbrev outE (i : Index ppref) : ℕ → ℕ → Cb.Gl.E := fun j v => ((i.val.H j v : ℤ) : Cb.Gl.E)

/-- The position coordinates that the calls' key points share. -/
abbrev posE (R : Model.Head.Run) : ℕ → Cb.Gl.E := fun j => pt Reading.gl R.x.Zl (R.h.ls + j)

/-- The calls' key points. -/
abbrev keyPtE (R : Model.Head.Run) : ℕ → ℕ → Cb.Gl.E :=
  fun q => pt Reading.gl (R.x.g1.zk.getD q #[])

/-- The keys under the verifier's names, at these cells. -/
abbrev kvE (R : Model.Head.Run) (Mz : Mats ℤ) (i : Index ppref) (x : Instance ppref) :
    String → ℕ → ℕ → Cb.Gl.E :=
  kvOf (Reading.gl.val (invE (Model.Head.pw (R.h.digSh + 15)))) HeadSizes.ref (npOf R.h)
    (cellsE R Mz) (outE i) (Cm.reqOf x)

/-- The verifier's padding key of call number q. -/
abbrev padKeyE (R : Model.Head.Run) (q : ℕ) : Cb.Gl.E :=
  Reading.gl.val (ofF ((R.L.cl.getD q default).tauAt (R.L.cl.getD q default).t0))

/-- What the first slot of the logits' sumcheck, scaled, is meant to hold. -/
def hdPart (R : Model.Head.Run) (t : Head.Cells Cb.Gl.E) (H : ℕ → ℕ → Cb.Gl.E) (y : Req)
    (u : ℕ → Cb.Gl.E) : Cb.Gl.E :=
  match (R.L.calls.getD R.x.qH default).seg? "HD0" with
  | some g => meantHD0 Reading.gl R R.x.qH HeadSizes.ref t H y u g
  | none => 0

/-- What the first slot of the sumcheck of stream and reciprocal is meant to hold. -/
def nfPart (R : Model.Head.Run) (t : Head.Cells Cb.Gl.E) (u : ℕ → Cb.Gl.E) : Cb.Gl.E :=
  ((R.L.calls.getD R.x.qN default).segs.map fun g =>
    if g.name = "NF" then meantNF Reading.gl R R.x.qN HeadSizes.ref t u g else 0).sum

/-- Values for the slots: A and B under the two slots sL and sL + 1; under the nine slots of the
sums of limb products, the seven of the row products and the first slots of two sumchecks what each
is meant to hold; 0 elsewhere. -/
def slotsFor (R : Model.Head.Run) (t : Head.Cells Cb.Gl.E) (H : ℕ → ℕ → Cb.Gl.E) (y : Req)
    (u v : ℕ → Cb.Gl.E) (sL : ℕ) (A B : Cb.Gl.E) (j : ℕ) : Cb.Gl.E :=
  if j = sL then A
  else if j = sL + 1 then B
  else if R.x.sW ≤ j ∧ j < R.x.sW + 9 then
    Blocks.ext R.h.lt (fun a => Ledger.Wsum nD (fun l k => bl t l k a) (j - R.x.sW)) v
  else if R.x.sPv ≤ j ∧ j < R.x.sPv + 7 then
    Blocks.ext R.h.lt (fun a => Ledger.prods (fun n => Dv t n a) (j - R.x.sPv)) v
  else if j = R.x.tN.sCl then nfPart R t u
  else if j = R.x.tH.sCl then ((2 : Cb.Gl.E) ^ R.h.lPd)⁻¹ * hdPart R t H y u
  else 0

/-- The order of the slots that are given a value. -/
structure SlotOrder (R : Model.Head.Run) (sL : ℕ) : Prop where
  a : sL + 1 < R.x.sW
  b : R.x.sW + 9 ≤ R.x.sPv
  c : R.x.sPv + 7 ≤ R.x.tN.sCl
  d : R.x.tN.sCl < R.x.tH.sCl

/-- The routine hear takes its slots in this order. -/
theorem slotOrder_of_hear {R : Model.Head.Run} {plain : Array E} {F G : Fork} {C D : Ctx}
    (hXL : R.h.XL = 5) (hx : Ok (Model.Head.hear R.h R.L R.hp R.cov plain) F C R.x G D) {sL : ℕ}
    (hsL : sL + 1 < R.x.sW) : SlotOrder R sL := by
  obtain ⟨a1, a2, a3, a4, a5⟩ := hear_slots_five hXL hx
  obtain ⟨_, _, _, _, _, _, b7, b8, _, _⟩ := hear_slots hx
  exact ⟨hsL, by omega, by omega, by omega⟩

section Values

variable {R : Model.Head.Run} {t : Head.Cells Cb.Gl.E} {H : ℕ → ℕ → Cb.Gl.E} {y : Req}
  {u v : ℕ → Cb.Gl.E} {sL : ℕ} {A B : Cb.Gl.E}

/-- The value under the first of the two slots of the lookup's end. -/
theorem slotsFor_sL : slotsFor R t H y u v sL A B sL = A := by
  unfold slotsFor
  rw [if_pos rfl]

/-- The value under the second of them. -/
theorem slotsFor_sR : slotsFor R t H y u v sL A B (sL + 1) = B := by
  unfold slotsFor
  rw [if_neg (Nat.succ_ne_self sL), if_pos rfl]

/-- The values under the slots of the sums of limb products. -/
theorem slotsFor_W (O : SlotOrder R sL) {s : ℕ} (hs : s < 9) :
    slotsFor R t H y u v sL A B (R.x.sW + s) =
      Blocks.ext R.h.lt (fun a => Ledger.Wsum nD (fun l k => bl t l k a) s) v := by
  have o1 := O.a
  have n1 : ¬ R.x.sW + s = sL := by omega
  have n2 : ¬ R.x.sW + s = sL + 1 := by omega
  have e : R.x.sW ≤ R.x.sW + s ∧ R.x.sW + s < R.x.sW + 9 := ⟨by omega, by omega⟩
  unfold slotsFor
  rw [if_neg n1, if_neg n2, if_pos e, Nat.add_sub_cancel_left]

/-- The values under the slots of the row products. -/
theorem slotsFor_P (O : SlotOrder R sL) {j : ℕ} (hj : j < 7) :
    slotsFor R t H y u v sL A B (R.x.sPv + j) =
      Blocks.ext R.h.lt (fun a => Ledger.prods (fun n => Dv t n a) j) v := by
  have o1 := O.a
  have o2 := O.b
  have n1 : ¬ R.x.sPv + j = sL := by omega
  have n2 : ¬ R.x.sPv + j = sL + 1 := by omega
  have n3 : ¬ (R.x.sW ≤ R.x.sPv + j ∧ R.x.sPv + j < R.x.sW + 9) := by omega
  have e : R.x.sPv ≤ R.x.sPv + j ∧ R.x.sPv + j < R.x.sPv + 7 := ⟨by omega, by omega⟩
  unfold slotsFor
  rw [if_neg n1, if_neg n2, if_neg n3, if_pos e, Nat.add_sub_cancel_left]

/-- The value under the first slot of the second token sumcheck. -/
theorem slotsFor_N (O : SlotOrder R sL) :
    slotsFor R t H y u v sL A B R.x.tN.sCl = nfPart R t u := by
  have o1 := O.a
  have o2 := O.b
  have o3 := O.c
  have n1 : ¬ R.x.tN.sCl = sL := by omega
  have n2 : ¬ R.x.tN.sCl = sL + 1 := by omega
  have n3 : ¬ (R.x.sW ≤ R.x.tN.sCl ∧ R.x.tN.sCl < R.x.sW + 9) := by omega
  have n4 : ¬ (R.x.sPv ≤ R.x.tN.sCl ∧ R.x.tN.sCl < R.x.sPv + 7) := by omega
  unfold slotsFor
  rw [if_neg n1, if_neg n2, if_neg n3, if_neg n4, if_pos rfl]

/-- The value under the first slot of the third token sumcheck. -/
theorem slotsFor_H (O : SlotOrder R sL) :
    slotsFor R t H y u v sL A B R.x.tH.sCl =
      ((2 : Cb.Gl.E) ^ R.h.lPd)⁻¹ * hdPart R t H y u := by
  have o1 := O.a
  have o2 := O.b
  have o3 := O.c
  have o4 := O.d
  have n1 : ¬ R.x.tH.sCl = sL := by omega
  have n2 : ¬ R.x.tH.sCl = sL + 1 := by omega
  have n3 : ¬ (R.x.sW ≤ R.x.tH.sCl ∧ R.x.tH.sCl < R.x.sW + 9) := by omega
  have n4 : ¬ (R.x.sPv ≤ R.x.tH.sCl ∧ R.x.tH.sCl < R.x.sPv + 7) := by omega
  have n5 : ¬ R.x.tH.sCl = R.x.tN.sCl := by omega
  unfold slotsFor
  rw [if_neg n1, if_neg n2, if_neg n3, if_neg n4, if_neg n5, if_pos rfl]

end Values

/-- One equation in two unknowns whose coefficients add up to 1 has a solution. -/
theorem solve_two {K : Type} [Field K] (t Q : K) : ∃ a b : K, (1 - t) * a + t * b = Q := by
  by_cases h : t = 0
  · exact ⟨Q, 0, by rw [h]; ring⟩
  · exact ⟨0, t⁻¹ * Q, by rw [mul_zero, zero_add, mul_inv_cancel_left₀ h]⟩

/-- The claim on the calls' key vectors without the hidden value at the end of the lookup's key
side. -/
def joinRest (R : Model.Head.Run) (fn : ℕ → ℕ → ℕ → Cb.Gl.E) (p : ℕ → ℕ → Cb.Gl.E) : Cb.Gl.E :=
  ∑ c ∈ range R.L.calls.size, Reading.gl.val (R.x.g1.e.getD c zeroE) *
      (Reading.gl.val R.x.g1.alpha - Reading.gl.val (ofF c.toUInt64) * Reading.gl.val R.x.g1.theta -
        Blocks.ext ((R.L.calls.getD c default).lJ + R.h.lt)
          (fun X => fn c (X / 2 ^ R.h.lt) (X % 2 ^ R.h.lt)) (p c)) +
    Reading.gl.val (emptyE R.x.g1)

/-- What the claim on the calls' key vectors is worth: joinRest less the hidden value at the end
of the lookup's key side. -/
theorem joinWorth_rest (W : World Cb.Gl.E) (R : Model.Head.Run) (fn : ℕ → ℕ → ℕ → Cb.Gl.E)
    (p : ℕ → ℕ → Cb.Gl.E) :
    joinWorth Reading.gl W R fn p = joinRest R fn p - R.x.g1.cEnd.value Reading.gl W := rfl

/-! ## 4. The whole -/

/-- What head_link_of_port (Johnson/Road/HeadLinkPort.lean) asks of the integer matrices Mz, the
world W and the calls' functions fn, but for two of the four clauses of its hypothesis ClaimsHold:
claimsL and claimsJ are the first two; the lookup's claims that read mask entries alone and its
three claims on the planes of the counts are not here. -/
structure LinkWorld (R : Model.Head.Run) (tl0 : Model.HTailF2) (F : Fork) (κ : ℕ → LayerScale)
    (tbs : ℕ → Tables) (i : Index ppref) (x : Instance ppref) (Mz : Mats ℤ) (W : World Cb.Gl.E)
    (fn : ℕ → ℕ → ℕ → Cb.Gl.E) : Prop where
  holds : ∀ Fn ∈ R.t.funs, Holds Reading.gl W tl0 R.iU3 (colsOf F R.iU3)
    (fun a r c => ((Mz a r c : ℤ) : Cb.Gl.E)) Fn
  small : ∀ a r c, |Mz a r c| < 2 ^ 18
  Kf : ∀ q w, (R.L.calls.getD q default).segs.foldlM
      (fun w g => Model.Head.markColumns R w g)
      (Array.replicate (R.L.calls.getD q default).J 0) = some w →
    KeyFn (R.L.calls.getD q default).segs w (R.L.calls.getD q default).J (kvE R Mz i x)
      (padKeyE R q) (fn q)
  claimsL : ∀ q5, RowOf R (colsOf F R.iU3) "P_V" q5 → ∀ k, k < 17 →
    ((ledCarries R q5 ++ ledTail R q5).getD k {}).value Reading.gl W = 0
  claimsJ : ∀ F4 c4 KF, Walk.Kept F F4 → FormsOf R F4 c4 KF →
    (joinForm R.x.g1 KF).value Reading.gl W = 0
  slots : SlotsHold Reading.gl W R (cellsE R Mz) (outE i) (Cm.reqOf x) (posE R)
  hW : ∀ s, s < 9 → W.slot (R.x.sW + s) = Blocks.ext R.h.lt (fun a => Ledger.Wsum nD
    (fun l j => bl (cellsE R Mz) l j a) s) (pt Reading.gl R.x.PV)
  hP : ∀ j, j < 7 → W.slot (R.x.sPv + j) = Blocks.ext R.h.lt (fun a => Ledger.prods
    (fun n => Dv (cellsE R Mz) n a) j) (pt Reading.gl R.x.PV)
  stepP : StepPoint (npOf R.h) (cellsE R Mz) R.h.lt (pt Reading.gl R.x.PV)
  stepL : StepLookupAt W R F fn (keyPtE R)
  layers : Top.LayersGive κ tbs i.val x.prompt (cellsH R.h R.L R.b Mz)

/-- The bundle LinkWorld can be met, given the shape of the hidden value at the end of the lookup's
key side (hEnd, hsL). -/
theorem link_met_end {R : Model.Head.Run} {tl0 : Model.HTailF2} {F F0 F1 F2 G2 : Fork}
    {C0 C1 C2 D2 : Ctx} {plain : Array E} {g : Model.Settings} {O : Model.Head.Owner}
    {NGr lkW : ℕ} {H0 : Model.Head.HPlanH2}
    (hy : Model.Head.layout R.h tauFCw = .ok R.L) (hFull : FullH R.h) (hsh : R.h.digSh = 8)
    (hF : R.h.famF = 24) (hTs : R.h.tabS = 4) (Bd : BorderH R.b)
    (hpl : Model.Head.planH2 g R.h R.L R.b O NGr lkW = .ok H0)
    (hm0 : R.hp.tl.mats = H0.tl.mats) (hN0 : R.hp.tl.NM = H0.tl.NM)
    (hd : C0.ch.dry = false) (hx : Ok (Model.Head.hear R.h R.L R.hp R.cov plain) F0 C0 R.x F1 C1)
    (ht : Ok (Model.Head.tablesOf R.h R.L R.hp R.cov R.x) F2 C2 R.t G2 D2)
    (hm : tl0.mats = R.hp.tl.mats) (hNM : tl0.NM = R.hp.tl.NM)
    {κ : ℕ → LayerScale} {tbs : ℕ → Tables} (hn : (npOf R.h).OK)
    (i : Index ppref) (x : Instance ppref)
    (Y : ReqFits R HeadSizes.ref (Cm.reqOf x))
    (htrue : RinfR ppref κ (npOf R.h) tbs ⟨0, 0, 0⟩ i x)
    {sL : ℕ} {tau : E}
    (hEnd : R.x.g1.cEnd =
      Aff.scale (Aff.slot sL) (subE oneE tau) + Aff.scale (Aff.slot (sL + 1)) tau)
    (hsL : sL + 1 < R.x.sW) :
    ∃ Mz W fn, LinkWorld R tl0 F κ tbs i x Mz W fn := by
  have Nu := numH_of_layout hFull hy
  have hpol : (⟨0, 0, 0⟩ : AcceptancePolicy).OK := ⟨by norm_num, by norm_num, by norm_num⟩
  obtain ⟨hl, hL0⟩ := Top.ledger_hyps_met (p := Cb.Gl.p) hn hpol i x htrue
  generalize Head.N.honCells (npOf R.h) (XK ppref κ tbs i.val x.prompt (2 * ppref.layers))
    i.val.H (Req.of ⟨0, 0, 0⟩ x) = tz at hl hL0
  have hL : Policy.LedgerHead.RF (F := Cb.Gl.E) (npOf R.h) (outE i) (Cm.reqOf x) tz :=
    Down.ledgerRF_gl.2 hL0
  have Sm : Policy.SameMain (cellsE R (matsFrom tz)) (tz.cast Cb.Gl.E) :=
    same_matsFrom Nu Bd tz
  have h2 : (2 : Cb.Gl.E) ≠ 0 := Policy.two_ne_GlE
  have hc := iw_23 gl_numerals gl_inverse h2 (R := R) hsh
  choose w hw using marks_of_layout (R := R) hy
  choose fn hfn using fun q => exists_keyFn (hw q) (kvE R (matsFrom tz) i x) (padKeyE R q)
  have Xh := View.heardFits_of_view hd hx
  have hPs := View.PV_size hd hx
  have Ord := slotOrder_of_hear hFull.XL hx hsL
  have A := callsAt_of_run Reading.gl hy Xh (callsLaid_of_layout hy)
  obtain ⟨a, b, hab⟩ := solve_two (Reading.gl.val tau) (joinRest R fn (keyPtE R))
  obtain ⟨W, hWs, hHolds⟩ := holdsH_met Reading.gl ht hm (colsOf F R.iU3)
    (fun a r c => ((matsFrom tz a r c : ℤ) : Cb.Gl.E))
    (slotsFor R (cellsE R (matsFrom tz)) (outE i) (Cm.reqOf x) (posE R) (pt Reading.gl R.x.PV)
      sL a b)
  have T := trueH_of_holds hpl hm0 hN0 hFull Nu Bd ht hm hNM hHolds
  have X := linesFit_of_run hy Xh Reading.gl (R := R) rfl rfl rfl hFull.lt hFull.d hFull.V hsh
    hFull.XL Y (reqOf_ok x) T
  have hPV := shortAt_of_sum hPs T.hrPV
  have hW : ∀ s, s < 9 → W.slot (R.x.sW + s) = Blocks.ext R.h.lt (fun a => Ledger.Wsum nD
      (fun l j => bl (cellsE R (matsFrom tz)) l j a) s) (pt Reading.gl R.x.PV) := by
    intro s hs
    rw [hWs]
    exact slotsFor_W Ord hs
  have hP : ∀ j, j < 7 → W.slot (R.x.sPv + j) = Blocks.ext R.h.lt (fun a => Ledger.prods
      (fun n => Dv (cellsE R (matsFrom tz)) n a) j) (pt Reading.gl R.x.PV) := by
    intro j hj
    rw [hWs]
    exact slotsFor_P Ord hj
  have S : SlotsHold Reading.gl W R (cellsE R (matsFrom tz)) (outE i) (Cm.reqOf x) (posE R) := by
    intro q hq
    obtain ⟨_, _, _, _, a5⟩ := A q hq
    refine ⟨fun g hg hname => ?_, ?_⟩
    · obtain ⟨f1, f2⟩ := (a5 g hg).1
      rw [hname] at f1 f2
      have eq : q = R.x.qH := Option.some.inj (f1.symm.trans Xh.qH)
      subst eq
      rw [hWs, slotsFor_H Ord, mul_inv_cancel_left₀ (pow_ne_zero _ h2)]
      unfold hdPart
      rw [f2]
    · by_cases hqN : q = R.x.qN
      · subst hqN
        rw [if_pos rfl, hWs, slotsFor_N Ord]
        rfl
      · refine nf_absent hqN fun g hg hname => ?_
        obtain ⟨f1, _⟩ := (a5 g hg).1
        rw [hname] at f1
        exact hqN (Option.some.inj (f1.symm.trans Xh.qN))
  have idns := idns_same Sm hL
  have keys := lookup_met gl_numerals hy hF hsh hTs
    (segsFit_of_layout hy hFull.lt hFull.d hFull.V hFull.XL) hc Sm hL hw hfn
  have hJ : joinWorth Reading.gl W R fn (keyPtE R) = 0 := by
    rw [joinWorth_rest, hEnd, Aff.value_add, Aff.value_scale, Aff.value_scale, Aff.value_slot,
      Aff.value_slot, hWs, slotsFor_sL, slotsFor_sR, Reading.gl.sub, Reading.gl.one, hab, sub_self]
  refine ⟨matsFrom tz, W, fn, ?_⟩
  exact {
    holds := hHolds
    small := matsFrom_small hL.small
    Kf := fun q w' hw' => by
      have e : w' = w q := Option.some.inj (hw'.symm.trans (hw q))
      rw [e]
      exact hfn q
    claimsL := fun q5 hq5 k hk => by
      rw [ledger_idn_plain gl_numerals hq5 hPV hk hW hP]
      refine Blocks.ext_zero_of_forall (fun a ha => idns a ?_ k hk) _
      rw [hFull.lt] at ha
      exact ha
    claimsJ := fun F4 c4 KF k4 hKF => by
      have X4 := X
      rw [← k4.2 R.iU3] at X4
      rw [joinForm_worth gl_numerals _ X4 A S hw hfn hKF]
      exact hJ
    slots := S
    hW := hW
    hP := hP
    stepP := fun _ => idns
    stepL := fun _ _ _ _ _ _ _ => keys
    layers := layersGive_matsFrom Nu Bd hl }

/-- **The bundle LinkWorld can be met**: the hypotheses of head_link_of_port on matrices, world and
functions but for the lookup's own claims. See the head of this file. For the whole of that
theorem's bundle see link_met_all in Johnson/Road/HeadLookMet.lean. -/
theorem link_met {R : Model.Head.Run} {tl0 : Model.HTailF2} {F F0 F1 F2 G2 : Fork}
    {C0 C1 C2 D2 : Ctx} {plain : Array E} {g : Model.Settings} {O : Model.Head.Owner}
    {NGr lkW : ℕ} {H0 : Model.Head.HPlanH2}
    (hy : Model.Head.layout R.h tauFCw = .ok R.L) (hFull : FullH R.h) (hsh : R.h.digSh = 8)
    (hF : R.h.famF = 24) (hTs : R.h.tabS = 4) (Bd : BorderH R.b)
    (hpl : Model.Head.planH2 g R.h R.L R.b O NGr lkW = .ok H0)
    (hm0 : R.hp.tl.mats = H0.tl.mats) (hN0 : R.hp.tl.NM = H0.tl.NM)
    (hd : C0.ch.dry = false) (hx : Ok (Model.Head.hear R.h R.L R.hp R.cov plain) F0 C0 R.x F1 C1)
    (ht : Ok (Model.Head.tablesOf R.h R.L R.hp R.cov R.x) F2 C2 R.t G2 D2)
    (hm : tl0.mats = R.hp.tl.mats) (hNM : tl0.NM = R.hp.tl.NM)
    {κ : ℕ → LayerScale} {tbs : ℕ → Tables} (hn : (npOf R.h).OK)
    (i : Index ppref) (x : Instance ppref)
    (Y : ReqFits R HeadSizes.ref (Cm.reqOf x))
    (htrue : RinfR ppref κ (npOf R.h) tbs ⟨0, 0, 0⟩ i x) :
    ∃ Mz W fn, LinkWorld R tl0 F κ tbs i x Mz W fn := by
  obtain ⟨sL, tau, hEnd, hsL⟩ := hear_end hx
  exact link_met_end hy hFull hsh hF hTs Bd hpl hm0 hN0 hd hx ht hm hNM hn i x Y htrue hEnd hsL

/-- head_link_of_port applies to a bundle LinkWorld, if the walk succeeds and the lookup's other
claims hold in the world (hrows, hplanes: the two clauses of ClaimsHold that the bundle lacks). This
shows that the fields of the bundle are that theorem's hypotheses letter by letter. It is no witness
for hrows and hplanes. -/
theorem LinkWorld.fits {R : Model.Head.Run} {tl tl' tl0 : Model.HTailF2}
    {wo : Model.WsForkOut} {Lc Lc' : Model.LinkCtx} {F G F0 F1 F2 G2 : Fork}
    {C D C0 C1 C2 D2 : Ctx} {plain : Array E}
    {g : Model.Settings} {O : Model.Head.Owner} {NGr lkW : ℕ} {H0 : Model.Head.HPlanH2}
    {κ : ℕ → LayerScale} {tbs : ℕ → Tables} {i : Index ppref} {x : Instance ppref} {Mz : Mats ℤ}
    {W : World Cb.Gl.E} {fn : ℕ → ℕ → ℕ → Cb.Gl.E} (B : LinkWorld R tl0 F κ tbs i x Mz W fn)
    (hrows : ∀ f ∈ R.x.g1.rows, f.value Reading.gl W = 0)
    (hplanes : ∀ F6 c6 A, Walk.Kept F F6 → PlanesOf R F6 c6 A →
      ∀ f ∈ A, f.value Reading.gl W = 0)
    (hy : Model.Head.layout R.h tauFCw = .ok R.L) (hFull : FullH R.h) (hsh : R.h.digSh = 8)
    (hF : R.h.famF = 24) (hTs : R.h.tabS = 4) (Bd : BorderH R.b)
    (hpl : Model.Head.planH2 g R.h R.L R.b O NGr lkW = .ok H0)
    (hm0 : R.hp.tl.mats = H0.tl.mats) (hN0 : R.hp.tl.NM = H0.tl.NM)
    (hd : C0.ch.dry = false) (hx : Ok (Model.Head.hear R.h R.L R.hp R.cov plain) F0 C0 R.x F1 C1)
    (ht : Ok (Model.Head.tablesOf R.h R.L R.hp R.cov R.x) F2 C2 R.t G2 D2)
    (hs : F.LS.size = F.ns) (hT : Walk.Keeps (tl.objectsF R.t.funs))
    (hwalk : Walk.OkL (Model.Head.walk R tl wo) Lc F C tl' Lc' G D)
    (hm : tl0.mats = R.hp.tl.mats) (hNM : tl0.NM = R.hp.tl.NM) (hn : (npOf R.h).OK)
    (hr : x.r = 1023) (he : x.e = 1024) (Y : ReqFits R HeadSizes.ref (Cm.reqOf x)) (pol : AcceptancePolicy) :
    RinfR ppref κ (npOf R.h) tbs pol i x :=
  head_link_of_port hy hFull hsh hF hTs Bd hpl hm0 hN0 hd hx ht hs hT hwalk hn i x hr he Y
    hm hNM B.holds B.small B.Kf ⟨B.claimsL, B.claimsJ, hrows, hplanes⟩ B.slots B.hW B.hP B.stepP
    B.stepL B.layers pol

/-- The bundle LinkWorld can be met together with the hypothesis LentH of head_link_seg
(Johnson/Road/HeadLinkSeg.lean). The lists Mg of the layers' groups are made from Mz: every matrix
of every list is the head's copy of the stream. So LentH holds by choice. This shows that the two
do not exclude each other, and nothing on the matrices of the layers' own sub-proofs. It is not
the whole bundle of head_link_seg, which asks all four clauses of ClaimsHold: for that see
seg_met_all in Johnson/Road/HeadLookMet.lean. -/
theorem seg_met {R : Model.Head.Run} {tl0 : Model.HTailF2} {F F0 F1 F2 G2 : Fork}
    {C0 C1 C2 D2 : Ctx} {plain : Array E} {g : Model.Settings} {O : Model.Head.Owner}
    {NGr lkW : ℕ} {H0 : Model.Head.HPlanH2}
    (hy : Model.Head.layout R.h tauFCw = .ok R.L) (hFull : FullH R.h) (hsh : R.h.digSh = 8)
    (hF : R.h.famF = 24) (hTs : R.h.tabS = 4)
    {hyL : Model.Layer.Shape} {pc : List (List String)} {y : Model.Layer.Lay}
    (hlay : Model.Layer.layout hyL pc = .ok y) (Sw : Switches hyL) (Z : Sized hyL All.DF)
    (Z2 : Sized2 hyL All.DF) (hb : R.b = Model.Verify.borderOf y)
    (hpl : Model.Head.planH2 g R.h R.L R.b O NGr lkW = .ok H0)
    (hm0 : R.hp.tl.mats = H0.tl.mats) (hN0 : R.hp.tl.NM = H0.tl.NM)
    (hd : C0.ch.dry = false) (hx : Ok (Model.Head.hear R.h R.L R.hp R.cov plain) F0 C0 R.x F1 C1)
    (ht : Ok (Model.Head.tablesOf R.h R.L R.hp R.cov R.x) F2 C2 R.t G2 D2)
    (hm : tl0.mats = R.hp.tl.mats) (hNM : tl0.NM = R.hp.tl.NM)
    {κ : ℕ → LayerScale} {tbs : ℕ → Tables} (hn : (npOf R.h).OK)
    (i : Index ppref) (x : Instance ppref)
    (Y : ReqFits R HeadSizes.ref (Cm.reqOf x))
    (htrue : RinfR ppref κ (npOf R.h) tbs ⟨0, 0, 0⟩ i x) :
    ∃ (Mz : Mats ℤ) (W : World Cb.Gl.E) (fn : ℕ → ℕ → ℕ → Cb.Gl.E) (Mg : ℕ → Mats ℤ),
      LinkWorld R tl0 F κ tbs i x Mz W fn ∧ LentH R.h y Mz (Mg 11) := by
  have Bd : BorderH R.b := by
    rw [hb]
    exact borderH_of_layout hlay Sw Z Z2
  obtain ⟨Mz, W, fn, B⟩ := link_met (F := F) hy hFull hsh hF hTs Bd hpl hm0 hN0 hd hx ht hm hNM hn
    i x Y htrue
  exact ⟨Mz, W, fn, fun _ _ r c => Mz (R.h.NHf + 3) r c, B, fun _ _ _ _ => rfl⟩

/-- A request as link_met asks for exists at the final normalisation 44, 30, 53,687, the numbers of
the full-size example that ships with the prover: at the library's reference scales. -/
theorem true_exists_ref : ∃ (i : Index ppref) (x : Instance ppref), x.r = 1023 ∧ x.e = 1024 ∧
    RinfR ppref Cm.sRef.kap ⟨44, 30, 53687⟩ (fun _ => tbRef) ⟨0, 0, 0⟩ i x := by
  obtain ⟨i, x, hr, he, ht⟩ := Top.next_true_exists Cm.lawful_sRef
  have hm := (Cm.trueAt_iff Cm.sRef.kap Cm.sRef.nf i x).1 ht
  exact ⟨i.index, x, hr, he,
    Top.rinfR_of_modelS ppref (by decide) Cm.sRef.kap Cm.sRef.nf (fun _ => tbRef) ⟨0, 0, 0⟩ i.index
      x hr he hm.2⟩

#print axioms sameZ_matsFrom
#print axioms matsFrom_small
#print axioms layersGive_matsFrom
#print axioms rows_kvOf
#print axioms lookup_met
#print axioms slotOrder_of_hear
#print axioms link_met
#print axioms LinkWorld.fits
#print axioms seg_met
#print axioms true_exists_ref

end OnBytes.Road.Hd
