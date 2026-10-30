-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Close/Law/FaTwoReaders.lean (kind K10): `faK10` MAY LAY ANOTHER SEED THAN THE
TABLE's READER OF SAMPLES GIVES, AS LONG AS THE TWO SEEDS HAVE ONE SAMPLE MAP AND THE ANSWERS ARE
THE SAME: THE DECODER AND "NO COLLISION" DO NOT PART. Definitions, statements and proofs.

Why. The table's reader of samples lays, for a message, SOME seed whose matrix on the message's real
entries is the sample row's form (`K1.smpAt`, Johnson/Desc/K1/Law/GoodSendForms.lean: a choice), not
the seed that the verifier drew. K10's condition in front asks more of the seed that fa lays: that
one function of it (pS) is the program's sample row's vector on the whole cube, the padding rows of
a member's block among them (`RowsTied`, AtPieceAll.lean). It is in doubt whether any pS
can meet that at the chosen seed. The letter smp of `faK10` (FaK10.lean, beside this file) is free:
it may be a reader of the drawn seed. What then ties fa to the table's pins and promise?
  `decMin_congr`, `clash_congr` (general): the library's decoder by a constrained minimum and its
    "collision" read the seed through `ev ρ` alone. `omsg_dec_congr`, `omsg_clash_congr`: so
    `OMsg.dec` and `OMsg.Clash` at two seeds with one `Z.val` (and the same answers) are one.
  `SameVal smpD smpT`: wherever the table's reader smpT gives a sample, the reader smpD gives one
    with the same `Z.val` at its seed and the same answers.
  `fa_decs_same`: under `SameVal`, where smpT gives a sample at i: the decoder at `faK10` with smpD
    is the decoder at `faK10` with smpT, at i. So every lemma that spends "the decoder at faK10
    (table's reader) gives u" (PinsAtFa.lean, MsgsAtFa.lean, PinsAtTable.lean) serves at `faK10`
    with smpD.
  `fa_front_same`: `K10On`'s clause front at `faK10` with smpD, from the table's "no collision"
    (`CfAt` at smpT), `SameVal`, and the joint's promise.
Limits. NO READER OF THE DRAWN SEED IS DEFINED HERE, and `SameVal` is shown of none: `K1.smpAt_of`
says, where the rows are the kind's one row at a seed ρ (`SeedIs`, `Tie`), that the chosen seed has
ρ's `Z.val`. Whether the doubt is founded (two drawn seeds with one matrix on the real entries and
different weights on a padding row) is not decided here. Nothing on soundness.

-/
import Johnson.Desc.First.Close.Law.FaK10

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Close

open scoped ENNReal
open OnBytes OnBytes.Slice OnBytes.Tie.Pv.Fold OnBytes.Flat OnBytes.Maker Iop IOR Prob Run KObj
open VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.BatFoldAt Cb Cb.Pv Johnson.Top.H
open VerifiableInference.Desc.Sound Johnson.Pack
open VerifiableInference.Desc (FileDescription Strs Wit)

variable {Xi : Type} (G : FileDescription Xi) (cs : OnBytes.Codes) (lo : List (OracleShape × ℕ))
  (seat : Fin lo.length → ℕ × ℕ)
variable (R : RowsK (sigOf cs lo)) (N : SlotNames R) (keep : (sigOf cs lo).O → Prop)
  [DecidablePred keep] {B : Type} [Fintype B] (pull : (R.Sh.Cin.J → GE) → R.G.C.J → GE) (n : ℕ)
  (num : R.G.Row B ≃ Fin n)
  (fx : Fin ((R.Sh.fold (SbV R B) (slV R pull) (ZV R n num)).n + 1) × GE) {Kc St₀ Wp : Type}
  {E₀ : ExtSpec}
  (A₀ : Rels Kc St₀ E₀ (((sigOf cs lo).sub (R.sizeB keep (SbV R B) (slV R pull)
    (ZV R n num)).kp).Msg × Wp))
  (bC bZ : ℕ) (w₀ : (sigOf cs lo).Wit × Wp)
  (w₁ : LdBrW R.G (R.sizeB keep (SbV R B) (slV R pull) (ZV R n num)).kp Wp)
  (L : List (BatFoldCaller GE))

local notation "S1" => VerifiableInference.Desc.First.S

set_option quotPrecheck false in
/-- The caller of the proved batching and fold. -/
local notation "CK" => R.foldCaller keep (SbV R B) (slV R pull) (ZV R n num) fx A₀ bC bZ w₀ w₁

/-- The decoder by a constrained minimum reads the seed through `ev ρ` alone. -/
theorem decMin_congr {T U D Y : Type} (dist rank : T → ℕ) (view : T → U) (ev : D → U → Y) (e : ℕ)
    (ρ ρ' : D) (y : Y) (h : ev ρ = ev ρ') :
    Cb.Ood.decMin dist rank view ev e ρ y = Cb.Ood.decMin dist rank view ev e ρ' y := by
  show Cb.Ood.decMin dist rank view (fun _ : Unit => ev ρ) e () y =
    Cb.Ood.decMin dist rank view (fun _ : Unit => ev ρ') e () y
  rw [h]

/-- So does "a collision". -/
theorem clash_congr {U D Y : Type} (Lst : U → Prop) (ev : D → U → Y) (ρ ρ' : D)
    (h : ev ρ = ev ρ') : Cb.Ood.Clash Lst ev ρ ↔ Cb.Ood.Clash Lst ev ρ' := by
  unfold Cb.Ood.Clash
  rw [h]

/-- **One sample map, the same answers: one decoded message.** -/
theorem omsg_dec_congr (o : OMsg GE) (f : o.Str) (σ σ' : o.Smp)
    (h1 : o.Z.val σ.1 = o.Z.val σ'.1) (h2 : σ.2 = σ'.2) : o.dec f σ = o.dec f σ' := by
  unfold OMsg.dec
  rw [h2]
  exact decMin_congr _ _ _ _ _ _ _ _ h1

/-- **One sample map: a collision at the one seed is a collision at the other.** -/
theorem omsg_clash_congr (o : OMsg GE) (f : o.Str) (ρ ρ' : o.Z.D)
    (h : o.Z.val ρ = o.Z.val ρ') : o.Clash f ρ ↔ o.Clash f ρ' :=
  clash_congr _ _ _ _ h

variable {Pz : Type}
  (smpD smpT : Pz × S1 → (i : Fin lo.length) → Option ((sigOf cs lo).om i).Smp)
  (σ₀ : (sigOf cs lo).Smp) (st₀ : St₀) (e₀ : E₀.Str) {F : Frame}
  (mW : S1 × F.E.Str → R.Sh.par.Cw.nat.Str)

/-- **Two readers of samples that the library cannot tell apart.** -/
def SameVal : Prop :=
  ∀ a i zz, smpT a i = some zz →
    ∃ zd, smpD a i = some zd ∧
      ((sigOf cs lo).om i).Z.val zd.1 = ((sigOf cs lo).om i).Z.val zz.1 ∧ zd.2 = zz.2

/-- **The decoder at what is laid does not part.** -/
theorem fa_decs_same (hV : SameVal cs lo smpD smpT) (z : Pz) (a : S1 × F.E.Str)
    (i : Fin lo.length) (zz : ((sigOf cs lo).om i).Smp) (hz : smpT (z, a.1) i = some zz) :
    (sigOf cs lo).decs (faK10 G cs lo seat R N keep pull n num fx A₀ bC bZ w₀ w₁ L smpD σ₀ st₀ e₀
        mW z a).1.2
      (faK10 G cs lo seat R N keep pull n num fx A₀ bC bZ w₀ w₁ L smpD σ₀ st₀ e₀ mW z a).2.1.2 i =
    (sigOf cs lo).decs (faK10 G cs lo seat R N keep pull n num fx A₀ bC bZ w₀ w₁ L smpT σ₀ st₀ e₀
        mW z a).1.2
      (faK10 G cs lo seat R N keep pull n num fx A₀ bC bZ w₀ w₁ L smpT σ₀ st₀ e₀ mW z a).2.1.2
      i := by
  obtain ⟨zd, hd, h1, h2⟩ := hV (z, a.1) i zz hz
  rw [fa_decs, fa_decs, hd, hz]
  exact omsg_dec_congr _ _ _ _ h1 h2

/-- **The proved sub-protocol's own promise in front, at the other reader.** -/
theorem fa_front_same (hV : SameVal cs lo smpD smpT) (z : Pz) (a : S1 × F.E.Str)
    (hc : ∀ i, CfAt G cs lo seat smpT i (z, a.1) (strsOf F a.2)) (hA : A₀.on (st₀, e₀)) :
    ((Cb.Pv.Bat.inJ (R.sizeB keep (SbV R B) (slV R pull) (ZV R n num)) A₀).keepE
      R.Sh.par.Cw.nat).on
      (faK10 G cs lo seat R N keep pull n num fx A₀ bC bZ w₀ w₁ L smpD σ₀ st₀ e₀ mW z a) := by
  refine fa_front G cs lo seat R N keep pull n num fx A₀ bC bZ w₀ w₁ L smpD σ₀ st₀ e₀ mW z a
    (fun i => ?_) hA
  obtain ⟨zz, hz, hs, hn⟩ := hc i
  obtain ⟨zd, hd, h1, -⟩ := hV (z, a.1) i zz hz
  exact ⟨zd, hd, hs, fun hcl => hn ((omsg_clash_congr _ _ _ _ h1).1 hcl)⟩

end VerifiableInference.Desc.First.Close

#print axioms VerifiableInference.Desc.First.Close.decMin_congr
#print axioms VerifiableInference.Desc.First.Close.clash_congr
#print axioms VerifiableInference.Desc.First.Close.omsg_dec_congr
#print axioms VerifiableInference.Desc.First.Close.omsg_clash_congr
#print axioms VerifiableInference.Desc.First.Close.fa_decs_same
#print axioms VerifiableInference.Desc.First.Close.fa_front_same
