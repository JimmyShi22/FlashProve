-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K11Caller/Items.lean: what stands open in front of and behind the merge of the claims on the weights, said plainly of the program's records and of three readings of a witness; each tied to
the typed record G.

Three letters read the committed values: cell r c (a cell of the committed matrix W), mask j (entry j of the sub-proof's mask row), idx j (entry j of the request's index-mask message).
    WeightsSays   IN FRONT: for each claim a: the sum that the claim speaks of (OnBytes.Road.claimVal, at the cells within W) is what was shown under its slot less the slot's factor times its mask entry
    MergedSays    BEHIND: the form of the claim that the merge's sumcheck leaves (Psc.rowForm at the shown end value) is worth 0 in the world of a ledger Fl at the mask row
    WoSays        BEHIND: the pending row as wsPending returns it: the sum over the cube's rows of (the returned vectors' entries) * (the row of W at the merge's point) + (entry c of the index-mask
                  message) * beta = target
    entries       the three readings as the entries of the record G at the slots' numbers (AtSlots.lean)
    weightsSays_iff   WeightsSays  ⇔  every claim of G holds at these entries
    woSays_iff        WoSays  ⇔  the row on the end value (MergeL.EV) holds at these entries, at a typed output that reads as the program's record
    merged_D1, merged_D2   at these entries and in MergedSays' world the two premises (D1), (D2) of the library's theorem on a sumcheck's row hold: so, by that theorem, MergedSays is the typed row claim
SPENT OF THE LIBRARY: nothing beyond what Prog.lean, AtSlots.lean and Port.lean spend.
Limits: definitions and identities: no random step. Who fills the three letters, and that what they read is committed before the merge's first draw, is not said. MergedSays is tied to the typed row claim
only through (D1), (D2): the theorem that spends them stands elsewhere. On hiding nothing.

-/
import Johnson.Top.H0.K11Caller.AtSlots
import Johnson.Top.H0.K11Caller.Port

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.K11Caller
open OnBytes
open OnBytes.Model (Reading World Fork Aff WsClaim WsForkOut WsPending wsPending wsForkStart wsClaimShape wsRowPart wsEpsT)
open OnBytes.Road (Numerals UnitOK rowAt claimVal)
open OnBytes.Road.Rows (pendWeight)
open Finset

variable {E' : Type} [Field E'] [Fintype E'] (ρ : Reading E') {P : Place} (N : Nums P)

/-- The three readings as the entries of the record. -/
def entries (cell : ℕ → ℕ → E') (mask idx : ℕ → E') : P.Cell ⊕ (Fin N.ns ⊕ Fin N.ni) → E'
  | .inl rc => cell rc.1.val rc.2.val
  | .inr (.inl j) => mask j.val
  | .inr (.inr j) => idx j.val

/-- The cells within W. -/
def cellsIn (P : Place) (cell : ℕ → ℕ → E') : OnBytes.Road.Wm E' := Wof P fun rc => cell rc.1.val rc.2.val

/-- **In front of the merge.** -/
def WeightsSays (st : MergeIn P.n) (cell : ℕ → ℕ → E') (mask : ℕ → E') : Prop :=
  ∀ a : Fin P.n, claimVal ρ P.lay (cellsIn P cell) (st.cl a) =
    ρ.val (st.F.vp.getD (N.sv a) zeroE) - ρ.val (st.F.mf.getD (N.sv a) zeroE) * mask (N.sv a)

/-- **Behind the merge: the claim that its sumcheck leaves.** Fl: the ledger at which the world is read. -/
def MergedSays (wo : WsForkOut) (Fl : Fork) (mask : ℕ → E') (entry : ℕ → ℕ → ℕ → E') : Prop :=
  (wo.p.rowForm wo.fvp {}).value ρ (Fl.worldOf ρ mask entry) = 0

/-- **Behind the merge: the pending row**, as wsPending returns it. -/
def WoSays (wo : WsForkOut) (claims : ℕ) (S : Params.LinShape) (cell : ℕ → ℕ → E') (idx : ℕ → E') : Prop :=
  ∀ w : WsPending, wsPending P.lay wo claims S = .ok w →
    ∑ j ∈ range (2 ^ S.kRow), pendWeight ρ w.g j * rowAt ρ P.lay.lk wo.rm (cellsIn P cell) j + idx N.c * ρ.val w.beta = ρ.val w.target

/-- The side condition that asks nothing. -/
abbrev noRd : MergeIn P.n → (P.Cell ⊕ (Fin N.ns ⊕ Fin N.ni) → E') → Prop := fun _ _ => True

/-- What is asked of the claims: each is on the place's unit, passes wsClaimShape, and its unit has OnBytes.Road.UnitOK. -/
structure ClaimsFit (P : Place) (st : MergeIn P.n) : Prop where
  ui : ∀ a, (st.cl a).ui = P.ui a
  shape : ∀ a, wsClaimShape P.lay (st.cl a) = .ok ()
  unit : ∀ a u, P.lay.U[P.ui a]? = some u → UnitOK P.lay.lk u

theorem ClaimsFit.fit {st : MergeIn P.n} (C : ClaimsFit P st) : Fit ρ P (Letters.atSlots ρ P N (noRd N)) st st.cl :=
  ⟨C.ui, C.shape, C.unit, fun _ => rfl⟩

variable {ρ} in
/-- **WeightsSays is: every claim of the typed record holds.** -/
theorem weightsSays_iff (hρ : Numerals ρ) (hk : 0 < P.lay.lk) (st : MergeIn P.n) (C : ClaimsFit P st) (cell : ℕ → ℕ → E') (mask idx : ℕ → E') :
    WeightsSays ρ N st cell mask ↔ ∀ a, (GS ρ N (noRd N)).Cl st (entries N cell mask idx) a := by
  refine forall_congr' fun a => ?_
  unfold Cb.Pv.Lay.WeightsL.Cl
  rw [G_val_means hρ P (Letters.atSlots ρ P N (noRd N)) st (entries N cell mask idx) st.cl hk (C.fit ρ N) a]
  show _ ↔ claimVal ρ P.lay (cellsIn P cell) (st.cl a) + mask (N.sv a) * ρ.val (st.F.mf.getD (N.sv a) zeroE) =
    ρ.val (st.F.vp.getD (N.sv a) zeroE)
  constructor
  · intro h
    rw [h]
    ring
  · intro h
    rw [← h]
    ring

variable {ρ} in
/-- **WoSays is the row on the end value**, at a typed output that reads as the program's record, where wsPending returns. -/
theorem woSays_iff (hρ : Numerals ρ) (hk : 0 < P.lay.lk) (o : (GS ρ N (noRd N)).L.T.par.Out) (C : ClaimsFit P o.st.1)
    (cell : ℕ → ℕ → E') (mask idx : ℕ → E') (rho : Fin P.n → E) (wo : WsForkOut) (hr : ∀ a, ρ.val (rho a) = o.st.2 ^ (a : ℕ))
    (hp : (GS ρ N (noRd N)).L.oPt o = pointOf ρ P.lay.lk wo.rm)
    (ho : wo.recs = (List.ofFn fun a => (o.st.1.cl a, rho a)).map fun y => wsRowPart P.lay y.1 (mulE y.2 (wsEpsT P.lay y.1 wo.rm)))
    (hb : (GS ρ N (noRd N)).L.oBe o = ρ.val wo.beta) (hv : o.vals () = ρ.val wo.fvp)
    {claims : ℕ} {S : Params.LinShape} {w : WsPending} (h : wsPending P.lay wo claims S = .ok w) :
    WoSays ρ N wo claims S cell idx ↔ (GS ρ N (noRd N)).L.EV o (entries N cell mask idx) := by
  rw [G_EV_row hρ P (Letters.atSlots ρ P N (noRd N)) o (entries N cell mask idx) o.st.1.cl rho wo hk (C.fit ρ N) hr hp ho hb hv h]
  constructor
  · intro H
    exact H w h
  · intro H w' h'
    have e : w' = w := Except.ok.inj (h'.symm.trans h)
    rw [e]
    exact H

omit [Fintype E'] in
/-- The mask row out of the entries is the mask row, at a slot. -/
theorem maskOf_entries (cell : ℕ → ℕ → E') (mask idx : ℕ → E') {j : ℕ} (hj : j < N.ns) : maskOf N (entries N cell mask idx) j = mask j := by
  unfold maskOf
  rw [dif_pos hj]
  rfl

omit [Fintype E'] in
/-- MergedSays' world meets the two conditions of AtSlots.lean, if the ledger Fl holds 0 and -1 under the sumcheck's own slots, and under the claims' slots what the state's ledger holds. -/
theorem merged_fits (st : MergeIn P.n) (cell : ℕ → ℕ → E') (mask idx : ℕ → E') (Fl : Fork) (entry : ℕ → ℕ → ℕ → E')
    (own : ∀ j, N.first ≤ j → j < N.first + 2 * P.lay.lk + 2 → Fl.vp.getD j zeroE = zeroE ∧ Fl.mf.getD j zeroE = subE zeroE oneE)
    (kept : ∀ a, Fl.vp.getD (N.sv a) zeroE = st.F.vp.getD (N.sv a) zeroE ∧ Fl.mf.getD (N.sv a) zeroE = st.F.mf.getD (N.sv a) zeroE) :
    Fits2 ρ N st (entries N cell mask idx) (Fl.worldOf ρ mask entry) where
  w1 := fun j h1 h2 => by
    obtain ⟨a, b⟩ := own j h1 h2
    rw [maskOf_entries N cell mask idx (by have := N.room; omega)]
    show ρ.val (Fl.vp.getD j zeroE) - ρ.val (Fl.mf.getD j zeroE) * mask j = _
    rw [a, b, ρ.sub, ρ.zero, ρ.one]
    ring
  w2 := fun a => by
    obtain ⟨h1, h2⟩ := kept a
    rw [maskOf_entries N cell mask idx (N.hsv a)]
    show ρ.val (Fl.vp.getD (N.sv a) zeroE) - ρ.val (Fl.mf.getD (N.sv a) zeroE) * mask (N.sv a) = _
    rw [h1, h2]

/-- **(D1) in MergedSays' world.** -/
theorem merged_D1 (x : MergeIn P.n × E') (cell : ℕ → ℕ → E') (mask idx : ℕ → E') (Fl : Fork) (entry : ℕ → ℕ → ℕ → E')
    (own : ∀ j, N.first ≤ j → j < N.first + 2 * P.lay.lk + 2 → Fl.vp.getD j zeroE = zeroE ∧ Fl.mf.getD j zeroE = subE zeroE oneE)
    (kept : ∀ a, Fl.vp.getD (N.sv a) zeroE = x.1.F.vp.getD (N.sv a) zeroE ∧ Fl.mf.getD (N.sv a) zeroE = x.1.F.mf.getD (N.sv a) zeroE) :
    (GS ρ N (noRd N)).L.toSum.T.par.W x (entries N cell mask idx) =
      OnBytes.Road.Hd.place (Fl.worldOf ρ mask entry).slot ((GS ρ N (noRd N)).L.toSum.T.par.vars x) N.first :=
  D1_at ρ N (noRd N) x _ _ (merged_fits ρ N x.1 cell mask idx Fl entry own kept)

/-- **(D2) in MergedSays' world.** -/
theorem merged_D2 (x : MergeIn P.n × E') (cell : ℕ → ℕ → E') (mask idx : ℕ → E') (Fl : Fork) (entry : ℕ → ℕ → ℕ → E')
    (own : ∀ j, N.first ≤ j → j < N.first + 2 * P.lay.lk + 2 → Fl.vp.getD j zeroE = zeroE ∧ Fl.mf.getD j zeroE = subE zeroE oneE)
    (kept : ∀ a, Fl.vp.getD (N.sv a) zeroE = x.1.F.vp.getD (N.sv a) zeroE ∧ Fl.mf.getD (N.sv a) zeroE = x.1.F.mf.getD (N.sv a) zeroE)
    (rho : Array E) (T : E) (h : x.1.F.publicPart (wsForkStart N.svA rho) = some T)
    (hr : ∀ a : Fin P.n, ρ.val (rho.getD a.val zeroE) = x.2 ^ (a : ℕ)) :
    (GS ρ N (noRd N)).L.toSum.T.par.inc x (entries N cell mask idx) = ρ.val T - (wsForkStart N.svA rho).value ρ (Fl.worldOf ρ mask entry) :=
  D2_at ρ N (noRd N) x _ _ (merged_fits ρ N x.1 cell mask idx Fl entry own kept) rho T h hr

end VerifiableInference.Desc.First.K11Caller

#print axioms VerifiableInference.Desc.First.K11Caller.merged_D1
#print axioms VerifiableInference.Desc.First.K11Caller.merged_D2
#print axioms VerifiableInference.Desc.First.K11Caller.weightsSays_iff
#print axioms VerifiableInference.Desc.First.K11Caller.woSays_iff
