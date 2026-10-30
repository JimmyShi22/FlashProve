-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/TiedLaidIn.lean: THE LAYING-IN: K10On's CLAUSE "tied"
(Johnson/Desc/First/Close/Law/OnK10.lean) AT faK10 (Close/Law/FaK10.lean) WITH THE
THREE TERMS LAID IN: smp := smpDrawn (DrawnSeed.lean) · num := numBy (TiedAtK10.lean) · pS := pSseed
(DrawnSeed.lean): FROM NAMED PREMISES ALONE. One statement and its proof: it shows that the terms
fit one another, and lists what is left.

  rowOfMsg T o     the first sample row of message number o in the statement T
  TiedOwes         WHAT IS LEFT, BY NAME, at a state a, its frame's group Gr and the begun
                   statement's layout lay: plain · gens (the two counts) · members (the group's
                   members are es' messages, in order) · seed (K1.SeedIs at some seed at every
                   member) · tie (K1.Tie of every member's shape) · plan (pSseed at the plan's T₀,
                   L₀ is pSseed at the state's) · inMain · inKept · inMask (where a message has a
                   weight, the entry lies inside its table) · fits (SampleFits of every member's
                   sample row)
  tied_laid_in     **TiedOwes ⊢ RowsTied at the three terms**: K10On's clause tied at that group
                   and layout

Limits. A JOINING. EVERY FIELD OF TiedOwes IS A PREMISE: none is shown of any state here. seed can
be had only along the narrower family of reached states (every word shown below the prime).
fits (SampleFits) is shown of nothing. At the frame's own group number.
No soundness statement.

-/
import Johnson.Desc.First.Close.Law.FaK10
import Johnson.Desc.First.Link.Law.TiedAtK10
import Johnson.Desc.First.Link.Law.DrawnSeed

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Close
open scoped ENNReal
open OnBytes OnBytes.Slice OnBytes.Slice.ProxRun OnBytes.Tie.Pv.Fold OnBytes.Flat OnBytes.Maker Iop
open IOR Prob Run KObj
open VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.BatFoldAt Cb Cb.Pv Johnson.Top.H
open VerifiableInference.Desc.Sound Johnson.Pack
open VerifiableInference.Desc (FileDescription Strs Wit)
open VerifiableInference.Desc.LinkJoin (numBy rowsTied_of smpDrawn smpDrawn_seed pSseed pSseed_eq
  namesOne_sampleRow)

attribute [local instance] Classical.propDecidable

/-- The first sample row of message number o. -/
def rowOfMsg (T : Statement) (o : ℕ) : OnBytes.Row :=
  (((T.oracles[o]?).map (·.sampleRows)).getD #[]).getD 0 default

variable {Xi : Type} (G : FileDescription Xi) (cs : OnBytes.Codes) (lo : List (OracleShape × ℕ))
  (seat : Fin lo.length → ℕ × ℕ) (seats : List (ℕ × ℕ))
variable (R : RowsK (sigOf cs lo)) (N : SlotNames R) (keep : (sigOf cs lo).O → Prop)
  [DecidablePred keep] (pull : (R.Sh.Cin.J → GE) → R.G.C.J → GE) (nP nG : ℕ)
  (es : List (Σ a : R.G.A, ((sigOf cs lo).om a.1).Z.S)) (nd : es.Nodup) (hall : ∀ x, x ∈ es)

local notation "S1" => VerifiableInference.Desc.First.S

set_option quotPrecheck false in
/-- The claim's rows: the plain rows and the generator rows. -/
local notation "BB" => (Fin nP ⊕ Fin nG)

set_option quotPrecheck false in
local notation "nn" => (nP + es.length + nG)

set_option quotPrecheck false in
local notation "NUM" => numBy nP nG es nd hall

set_option quotPrecheck false in
/-- A member's message's fixed number. -/
local notation "noOf" => fun i : Fin lo.length => numAt seats ⟨⟨lo, seat⟩, i⟩

variable (fx : Fin ((R.Sh.fold (SbV R (Fin nP ⊕ Fin nG)) (slV R pull)
    (ZV R (nP + es.length + nG) (numBy nP nG es nd hall))).n + 1) × GE)
  {Kc St₀ Wp : Type} {E₀ : ExtSpec}
  (A₀ : Rels Kc St₀ E₀ (((sigOf cs lo).sub (R.sizeB keep (SbV R (Fin nP ⊕ Fin nG)) (slV R pull)
    (ZV R (nP + es.length + nG) (numBy nP nG es nd hall))).kp).Msg × Wp))
  (bC bZ : ℕ) (w₀ : (sigOf cs lo).Wit × Wp)
  (w₁ : LdBrW R.G (R.sizeB keep (SbV R (Fin nP ⊕ Fin nG)) (slV R pull)
    (ZV R (nP + es.length + nG) (numBy nP nG es nd hall))).kp Wp)
  (L : List (BatFoldCaller GE)) {Pz : Type}
  (σ₀ : (sigOf cs lo).Smp) (st₀ : St₀) (e₀ : E₀.Str) {F : Frame}
  (mW : VerifiableInference.Desc.First.S × F.E.Str → R.Sh.par.Cw.nat.Str) (T₀ : Statement)
  (L₀ : GroupLayout)

set_option quotPrecheck false in
/-- faK10 with the reader of a seed that makes the row, and the numbering numBy. -/
local notation "FA" => faK10 G cs lo seat R N keep pull nn NUM fx A₀ bC bZ w₀ w₁ L
  (fun (a : Pz × S1) i => smpDrawn cs seats a ⟨lo, seat⟩ i) σ₀ st₀ e₀ mW

/-- **WHAT IS LEFT OF "tied", BY NAME.** -/
structure TiedOwes (z : Pz) (a : S1 × F.E.Str) (Gr : Group) (lay : GroupLayout) : Prop where
  plain : (Gr.rows.filter (·.kind == .plain)).toList.length = nP
  gens : (Gr.rows.filter (·.kind == .generator)).toList.length = nG
  members : Gr.members.toList = es.map fun x => noOf x.1.1
  seed : ∀ x : (Σ a : R.G.A, ((sigOf cs lo).om a.1).Z.S),
    ∃ (ρ : (Fin (bitsZ cs (lo.get x.1.1).1) → GE) × GEˣ) (y : GE),
      K1.SeedIs cs (lo.get x.1.1).1 a.1.st (noOf x.1.1) ρ y
  tie : ∀ x : (Σ a : R.G.A, ((sigOf cs lo).om a.1).Z.S), K1.Tie cs (lo.get x.1.1).1
  plan : ∀ as D, pSseed cs lo R N T₀ L₀ noOf as D =
    pSseed cs lo R N (begun (rdK a.1).2.2 (rdK a.1).2.1.group Gr) lay noOf as D
  inMain : ∀ (as : Σ a : R.G.A, ((sigOf cs lo).om a.1).Z.S) (b : Fin (R.s.h + R.s.g) → Bool)
    (x : Fin R.s.C.l),
    mainWeight (K := GE) (begun (rdK a.1).2.2 (rdK a.1).2.1.group Gr) lay (noOf as.1.1)
      (Sz.rowNo b + 2 ^ (R.s.h + R.s.g) * x.val) ≠ 0 →
    mainBack (begun (rdK a.1).2.2 (rdK a.1).2.1.group Gr) lay (noOf as.1.1)
      (Sz.rowNo b + 2 ^ (R.s.h + R.s.g) * x.val) <
        2 ^ (K1.Msg.of cs (lo.get as.1.1).1).bits .main
  inKept : ∀ (as : Σ a : R.G.A, ((sigOf cs lo).om a.1).Z.S) (q : R.Kp) (x : Fin R.s.C.l),
    N.orc q = noOf as.1.1 → N.idx q x < 2 ^ (K1.Msg.of cs (lo.get as.1.1).1).bits .main
  inMask : ∀ (as : Σ a : R.G.A, ((sigOf cs lo).om a.1).Z.S) (b : Fin R.s.h → Bool)
    (x : Fin R.s.Z.l),
    maskWeight (K := GE) (begun (rdK a.1).2.2 (rdK a.1).2.1.group Gr) lay (noOf as.1.1)
      (Sz.rowNo b + 2 ^ R.s.h * x.val) ≠ 0 →
    maskBack (begun (rdK a.1).2.2 (rdK a.1).2.1.group Gr) lay (noOf as.1.1)
      (Sz.rowNo b + 2 ^ R.s.h * x.val) < 2 ^ (K1.Msg.of cs (lo.get as.1.1).1).bits .mask
  fits : ∀ as : (Σ a : R.G.A, ((sigOf cs lo).om a.1).Z.S),
    SampleFits N (begun (rdK a.1).2.2 (rdK a.1).2.1.group Gr) lay (rowOfMsg a.1.st (noOf as.1.1))
      (noOf as.1.1) as.1 (Slf.atMem (Jf := fun a : R.G.A => ((sigOf cs lo).om a.1).C.J) as.1
        (((sigOf cs lo).om as.1.1).row as.2) ((FA z a).1.2 as.1.1).1)

/-- **K10On's CLAUSE tied, AT THE THREE TERMS.** -/
theorem tied_laid_in (z : Pz) (a : S1 × F.E.Str) (Gr : Group) (lay : GroupLayout)
    (hG : (rdK a.1).2.2.groups[(rdK a.1).2.1.group]? = some Gr)
    (hl : (begun (rdK a.1).2.2 (rdK a.1).2.1.group Gr).layout (rdK a.1).2.1.group = some lay)
    (O : TiedOwes G cs lo seat seats R N keep pull nP nG es nd hall fx A₀ bC bZ w₀ w₁ L σ₀ st₀ e₀
      mW T₀ L₀ z a Gr lay) :
    RowsTied R nn NUM N (pSseed cs lo R N T₀ L₀ noOf) (FA z a).1.1.1 (FA z a).1.2
      (begun (rdK a.1).2.2 (rdK a.1).2.1.group Gr) lay (runRows (rdK a.1).2.2 Gr).toList := by
  have hrow : ∀ x : (Σ a : R.G.A, ((sigOf cs lo).om a.1).Z.S),
      ((((rdK a.1).2.2).oracles[noOf x.1.1]?).map (·.sampleRows)).getD #[] =
        #[rowOfMsg a.1.st (noOf x.1.1)] := by
    intro x
    obtain ⟨ρ, y, -, orc, zz, β, t, hx, -, -, hr, -, -⟩ := O.seed x
    have hx' : ((rdK a.1).2.2).oracles[noOf x.1.1]? = some orc := hx
    unfold rowOfMsg
    rw [hx', hx]
    simp [hr]
  refine rowsTied_of R N _ (rdK a.1).2.2 Gr _ lay nP nG O.plain O.gens es nd hall
    (fun x => noOf x.1.1) O.members (fun x => rowOfMsg a.1.st (noOf x.1.1))
    (fun x _ => hrow x) _ _ (fun hn b => fa_claim G cs lo seat R N keep pull nn NUM fx A₀ bC bZ w₀
      w₁ L _ σ₀ st₀ e₀ mW z a Gr lay hG hl hn b) (fun as => ?_)
  obtain ⟨ρ, y, hsm, hS⟩ := smpDrawn_seed (P := Pz) cs seats (z, a.1) ⟨lo, seat⟩ as.1.1 (O.seed as)
  have hσ : (FA z a).1.2 as.1.1 = (ρ, fun _ => y) := by
    show ((smpDrawn cs seats (z, a.1) ⟨lo, seat⟩ as.1.1).getD (σ₀ as.1.1)) = _
    rw [hsm]
    rfl
  obtain ⟨-, orc, zz, β, t, hx, -, -, hr, hread, ht⟩ := hS
  have hro : rowOfMsg a.1.st (noOf as.1.1) =
      K1.sampleRow (K1.Msg.of cs (lo.get as.1.1).1) (noOf as.1.1) zz β 0 t := by
    unfold rowOfMsg
    have hx' : a.1.st.oracles[noOf as.1.1]? = some orc := hx
    rw [hx']
    simp [hr]
  beta_reduce at hro
  refine ⟨?_, ?_, noOf as.1.1, ?_, O.fits as⟩
  · beta_reduce
    rw [hσ, hro]
    exact ht.symm
  · beta_reduce
    rw [hσ, O.plan, hro]
    exact pSseed_eq cs lo R N _ lay noOf as (O.tie as) zz β t ρ hread (O.inMain as) (O.inKept as)
      (O.inMask as)
  · beta_reduce
    rw [hro]
    exact namesOne_sampleRow _ _ _ _ _ _

end VerifiableInference.Desc.First.Close

#print axioms VerifiableInference.Desc.First.Close.tied_laid_in
