-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Close/Law/FaK10.lean (kind K10): A CONCRETE TERM FOR THE LETTER fa OF K10's LAW:
what is laid in front of the proved batching and fold, off the verifier's state and the oracles'
strings. A definition, statements and proofs.

Why. K10's law (`k10_goodIn`, GoodOf.lean; `k10_law_full_lay`, KindK10LawLay.lean, beside this file)
is typed over a letter fa : the state with its strings -> the proved sub-protocol's statement with
its oracles. Its condition in front (`K10On`, OnK10.lean) and its end (`K10EndS`) speak of fa's
value alone: no premise ties that value to the table of joints' own readings. The table's files
read a sending's members by `wordsOf`, `PinAt`, `CfAt` (Johnson/Desc/Sound/MsgSig.lean), over the
SAME signature `sigOf cs lo` and the SAME decoder with a sample. Here fa is laid of these readings.
  `faK10 .. z a`: the claim's rows: the target and the vector (`rowVec`) of the row at the number
    that num gives, among the rows that the frame's group's test takes in (`runRows`), at the begun
    statement's layout; 0 where there is none · the kept messages' joint's statement and strings:
    letters (st₀, e₀) · THE SAMPLES: what the table's reader smp gives at the state; a letter σ₀
    where it gives nothing · THE WORDS: `wordsOf G cs lo seat` of the strings · the mask's word: a
    letter mW.
  `fa_decs`: the proved sub-protocol's decoder at what fa lays IS the library's decoder at the
    table's word and the sample laid: by definition.
  `fa_front`: `K10On`'s clause front at faK10, from: every member has no collision in the table's
    sense (`CfAt`), and the joint A₀'s promise at the two letters.
  `fa_pin`: where the state holds member i's sample, every leaf is shown, fa's decoder gives m at i,
    and the witness's message at i is m: member i is pinned in the table's sense (`PinAt`).
  `fa_claim`: the first half of `RowsTied` (AtPieceAll.lean) at faK10: where the group and the
    layout are there and the rows are n: by the make.
Limits. A DEFINITION AND FOUR SMALL LEMMAS: NO LAW. The second half of `RowsTied` (the samples'
rows) is not treated. st₀, e₀, σ₀, mW, pS, N, num and the joint A₀ are letters. That cs is the
statement's table of codes, lo the link's written list, seat the plan's seats, is said nowhere here.
Nothing on soundness.

-/
import Johnson.Desc.First.Close.Law.OnK10
import Johnson.Desc.First.Close.Law.FrontOn
import Johnson.Desc.First.Close.Law.AtBlockSelf
import Johnson.Desc.Sound.MsgSig

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

variable {Pz : Type}
  (smp : Pz × S1 → (i : Fin lo.length) → Option ((sigOf cs lo).om i).Smp)
  (σ₀ : (sigOf cs lo).Smp) (st₀ : St₀) (e₀ : E₀.Str) {F : Frame}
  (mW : S1 × F.E.Str → R.Sh.par.Cw.nat.Str)

/-- The row number i among the rows that the frame's group's test takes in. -/
def rowK10 (s : S1) (i : ℕ) : Option OnBytes.Row :=
  ((rdK s).2.2.groups[(rdK s).2.1.group]?).bind fun Gr => (runRows (rdK s).2.2 Gr).toList[i]?

/-- Its vector on the fold's input code, at the begun statement's layout; 0 where there is none. -/
noncomputable def vecK10 (s : S1) (i : ℕ) : R.Sh.Cin.J → GE :=
  match (rdK s).2.2.groups[(rdK s).2.1.group]? with
  | some Gr =>
    match (begun (rdK s).2.2 (rdK s).2.1.group Gr).layout (rdK s).2.1.group,
      (runRows (rdK s).2.2 Gr).toList[i]? with
    | some lay, some r => rowVec N (begun (rdK s).2.2 (rdK s).2.1.group Gr) lay r
    | _, _ => fun _ => 0
  | none => fun _ => 0

/-- **WHAT IS LAID IN FRONT OF THE PROVED SUB-PROTOCOL.** -/
noncomputable def faK10 (z : Pz) (a : S1 × F.E.Str) :
    ((kBatFoldRide L).src (CK)).X × ((kBatFoldRide L).src (CK)).E.Str :=
  (((((fun b => ((rowK10 a.1 (num (.inl b)).val).map fun r => readE r.target).getD 0),
      (fun b => vecK10 cs lo R N a.1 (num (.inl b)).val)), st₀),
    fun i => (smp (z, a.1) i).getD (σ₀ i)),
    ((e₀, wordsOf G cs lo seat (strsOf F a.2)), mW a))

/-- The decoder at what is laid is the library's, at the table's word and the sample laid. -/
theorem fa_decs (z : Pz) (a : S1 × F.E.Str) (i : Fin lo.length) :
    (sigOf cs lo).decs (faK10 G cs lo seat R N keep pull n num fx A₀ bC bZ w₀ w₁ L smp σ₀ st₀ e₀ mW
        z a).1.2
      (faK10 G cs lo seat R N keep pull n num fx A₀ bC bZ w₀ w₁ L smp σ₀ st₀ e₀ mW z a).2.1.2 i =
      ((sigOf cs lo).om i).dec (wordsOf G cs lo seat (strsOf F a.2) i)
        ((smp (z, a.1) i).getD (σ₀ i)) := rfl

/-- **The proved sub-protocol's own promise in front, from the table's "no collision".** -/
theorem fa_front (z : Pz) (a : S1 × F.E.Str)
    (hc : ∀ i, CfAt G cs lo seat smp i (z, a.1) (strsOf F a.2)) (hA : A₀.on (st₀, e₀)) :
    ((Cb.Pv.Bat.inJ (R.sizeB keep (SbV R B) (slV R pull) (ZV R n num)) A₀).keepE
      R.Sh.par.Cw.nat).on
      (faK10 G cs lo seat R N keep pull n num fx A₀ bC bZ w₀ w₁ L smp σ₀ st₀ e₀ mW z a) := by
  refine (front_on _ _ _ _).2 ⟨fun i => ?_, hA⟩
  obtain ⟨zz, hz, -, hn⟩ := hc i
  show ¬ ((sigOf cs lo).om i).Clash (wordsOf G cs lo seat (strsOf F a.2) i)
    ((smp (z, a.1) i).getD (σ₀ i)).1
  rw [hz]
  exact hn

/-- **A member that decodes at what is laid is pinned in the table's sense**, at a witness that
holds the decoded message. -/
theorem fa_pin {Cells Tok : Type} (arr : ℕ → ℕ → ℕ) (z : Pz) (a : S1 × F.E.Str)
    (i : Fin lo.length) (w : Wit Cells Tok MsgT) (zz : ((sigOf cs lo).om i).Smp)
    (hz : smp (z, a.1) i = some zz) (hs : ShownAt G cs lo seat (strsOf F a.2) i)
    (m : ((sigOf cs lo).om i).Msg)
    (hd : (sigOf cs lo).decs (faK10 G cs lo seat R N keep pull n num fx A₀ bC bZ w₀ w₁ L smp σ₀ st₀
        e₀ mW z a).1.2
      (faK10 G cs lo seat R N keep pull n num fx A₀ bC bZ w₀ w₁ L smp σ₀ st₀ e₀ mW z a).2.1.2 i =
      some m)
    (hw : msgsOf cs lo seat arr w i = m) :
    PinAt G cs lo seat smp arr i (z, a.1) (strsOf F a.2) w := by
  refine ⟨zz, hz, hs, ?_⟩
  rw [fa_decs, hz] at hd
  rw [hw]
  exact hd

/-- **The claim's rows are tied, by the make**: the first half of `RowsTied`. -/
theorem fa_claim (z : Pz) (a : S1 × F.E.Str) (Gr : Group) (lay : GroupLayout)
    (hG : (rdK a.1).2.2.groups[(rdK a.1).2.1.group]? = some Gr)
    (hl : (begun (rdK a.1).2.2 (rdK a.1).2.1.group Gr).layout (rdK a.1).2.1.group = some lay)
    (hn : (runRows (rdK a.1).2.2 Gr).toList.length = n) (b : B) :
    (faK10 G cs lo seat R N keep pull n num fx A₀ bC bZ w₀ w₁ L smp σ₀ st₀ e₀ mW z a).1.1.1.1 b =
        readE ((runRows (rdK a.1).2.2 Gr).toList[(num (.inl b)).val]'(hn ▸
          (num (.inl b)).isLt)).target ∧
      (faK10 G cs lo seat R N keep pull n num fx A₀ bC bZ w₀ w₁ L smp σ₀ st₀ e₀ mW z a).1.1.1.2 b =
        rowVec N (begun (rdK a.1).2.2 (rdK a.1).2.1.group Gr) lay
          ((runRows (rdK a.1).2.2 Gr).toList[(num (.inl b)).val]'(hn ▸ (num (.inl b)).isLt)) := by
  have hi : (num (.inl b)).val < (runRows (rdK a.1).2.2 Gr).toList.length :=
    hn ▸ (num (.inl b)).isLt
  constructor
  · show ((rowK10 a.1 (num (.inl b)).val).map fun r => readE r.target).getD 0 = _
    unfold rowK10
    rw [hG, Option.bind_some, List.getElem?_eq_getElem hi]
    rfl
  · show vecK10 cs lo R N a.1 (num (.inl b)).val = _
    unfold vecK10
    rw [hG]
    simp only [hl, List.getElem?_eq_getElem hi]

end VerifiableInference.Desc.First.Close

#print axioms VerifiableInference.Desc.First.Close.fa_decs
#print axioms VerifiableInference.Desc.First.Close.fa_front
#print axioms VerifiableInference.Desc.First.Close.fa_pin
#print axioms VerifiableInference.Desc.First.Close.fa_claim
