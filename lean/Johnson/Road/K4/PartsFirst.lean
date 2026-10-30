-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/PartsFirst.lean: THE FIRST GROUP's twin of Johnson/Road/K4/PartsOfValues.lean and
PartsOfClaims.lean: eight parts of the library's ledger of the first group's layers' sub-proof
(clFirst, Cb/Pv/Lay/End/LayFirst.lean) hold of entries y, where the claims of K4's run "front" are
worth 0 and the dictionary FrontDict holds.

The first group's chain has its own letters (FullFPar; the chain's last statements (tailW P).s7.Nx;
the norms' record eAtF). Each part of clFirst is, as in a later group, the ledger ledOf of a list of
forms, and the lists are the same lists at these letters. FrontDict and values_of_front
(Johnson/Road/K4/ValuesOfClaims.lean) are general in the names and the records: so they serve here
as they stand. One part more: emb, the embedding's one claim.

Main names:
  `sqF_holds`, `batF_holds`, `ledF_holds`, `termsF_holds`, `gatedF_holds`, `hotF_holds`,
    `stackF_holds`, `embF_holds`: each part from its forms worth 0. Bookkeeping.
  `parts_of_claims_first`: the eight parts, from FrontDict at the first group's letters, the zeros
    of the run "front", the five claims that the sumchecks themselves leave, the two claims on the
    form parts of the batched sumcheck's sides, and the embedding's claim.
Limits. All of these are premises; the embedding's claim worth 0 at y among them (no port of it is
called here). The parts merge, look and planes are not spoken of. With routed experts and a second
product layer alone. Implications in a given world: no draw, nothing on soundness or on hiding.


-/
import Johnson.Road.K4.ValuesOfClaims
import Cb.Pv.Lay.End.LayFirst

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open TWhole Cb Cb.Sub Cb.Pv.Lay Cb.Pv.Lay.At Cb.Pv.Lay.End Cb.Pv.Lay.End.Gated
open Inst.Model (Scl)
open OnBytes.Model (Reading World Fork Level)
open OnBytes.Model.Layer (Pub Own)

variable {E : Type} [Field E] [Fintype E] [scl : Scl] {M X : Type} (P : FullFPar E M X)
  {Nm J₂ : Type} [Fintype J₂] [DecidableEq J₂] (Y : LateLay Nm J₂) (ιN : NormsNm → Nm)
  (ιT : TermsNm → Nm) (ιG : GatedNm → Nm) (ιE : EmbNm → Nm)
  (R : (tailW P).s7.Nx → Rest2 E (P.J ⊕ J₂)) (zt : (tailW P).s7.Nx → ℕ → E) (b B sG : ℕ)
  (e : (tailW P).s7.Nx) (y : P.J ⊕ J₂ → E)

/-- The part sq. -/
theorem sqF_holds (h1 : Blocks.Form.val y (u1At P.ofp.nr ((tailW P).b1 e).2) = 0)
    (h2 : Blocks.Form.val y
      (cSame (namesAt P.ofp.nr (readsAt Y ιN)) (eAtF P.ofp P.wfPart e (zt e))) = 0)
    (h3 : Blocks.Form.val y
      (Cb.Pv.Lay.End.cEnd (namesAt P.ofp.nr (readsAt Y ιN)) (eAtF P.ofp P.wfPart e (zt e))
        (P.D.lL + 1) b B P.D.nNu) = 0) :
    Ledger.Holds (clFirst P Y ιN ιT ιG ιE R zt b B sG e).sq y := by
  have k : Ledger.Holds (sqAtF P.ofp P.wfPart Y ιN e (zt e) b B) y := by
    unfold sqAtF
    refine (ledOf_holds _ y).2 fun f hf => ?_
    simp only [clNorms, List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl
    · exact h1
    · exact h2
    · exact h3
  exact k

/-- The part bat. -/
theorem batF_holds (h : Blocks.Form.val y
      (cBatch (namesAt P.ofp.nr (readsAt Y ιN)) (eAtF P.ofp P.wfPart e (zt e)) P.D.nNu) = 0) :
    Ledger.Holds (clFirst P Y ιN ιT ιG ιE R zt b B sG e).bat y := by
  have k : Ledger.Holds (batAtF P.ofp P.wfPart Y ιN e (zt e)) y := by
    unfold batAtF
    refine (ledOf_holds _ y).2 fun f hf => ?_
    rw [List.mem_singleton] at hf
    rw [hf]
    exact h
  exact k

/-- The part led. -/
theorem ledF_holds (hu : Blocks.Form.val y (u2At P.ofp.nr ((tailW P).b2 e).2) = 0)
    (u : Blocks.Form (P.J ⊕ J₂) E)
    (h : ∀ q ∈ (clLedger (namesAt P.ofp.nr (readsAt Y ιN)) (eAtF P.ofp P.wfPart e (zt e)) u
      P.D).tail, Blocks.Form.val y q = 0) :
    Ledger.Holds (clFirst P Y ιN ιT ιG ιE R zt b B sG e).led y := by
  have k : Ledger.Holds (rowsAtF P.ofp P.wfPart Y ιN e (zt e)) y := by
    unfold rowsAtF
    refine (ledOf_holds _ y).2 fun f hf => ?_
    rcases List.mem_cons.mp hf with rfl | hf'
    · exact hu
    · exact h f hf'
  exact k

/-- The part terms. -/
theorem termsF_holds
    (h : ∀ q ∈ termsCl (namesT P.tp (readsT Y ιT)) (termsEAt P.tp ((tailW P).b3 e).2) P.D,
      Blocks.Form.val y q = 0) :
    Ledger.Holds (clFirst P Y ιN ιT ιG ιE R zt b B sG e).terms y := by
  have k : Ledger.Holds (termsLed P.tp (readsT Y ιT) ((tailW P).b3 e).2) y := by
    unfold termsLed
    exact (ledOf_holds _ y).2 h
  exact k

/-- The part gated. -/
theorem gatedF_holds (h5 : Blocks.Form.val y (prodU P.fp.gp ((tailW P).b5 e).2) = 0)
    (h6 : Blocks.Form.val y (prodU P.fp.rt.L ((tailW P).b6 e).2) = 0)
    (h : ∀ q ∈ gatedCl (gNamesAt P.fp (gReadsAt Y ιG))
      (gatedEAt P.fp ((tailW P).b5 e).2 ((tailW P).b6 e).2) P.D sG, Blocks.Form.val y q = 0) :
    Ledger.Holds (clFirst P Y ιN ιT ιG ιE R zt b B sG e).gated y := by
  have k : Ledger.Holds
      (gatedLedOf P.fp Y ιG ((tailW P).b5 e).2 ((tailW P).b6 e).2 sG) y := by
    unfold gatedLedOf gatedLed
    refine (ledOf_holds _ y).2 fun f hf => ?_
    rcases (mem_two_two _ _ _ _).1 hf with rfl | rfl | hf'
    · exact h5
    · exact h6
    · exact h f hf'
  exact k

/-- The part hot. -/
theorem hotF_holds
    (h : ∀ q ∈ clHot (E := E) (namesAt P.ofp.nr (readsAt Y ιN)) P.D, Blocks.Form.val y q = 0) :
    Ledger.Holds (clFirst P Y ιN ιT ιG ιE R zt b B sG e).hot y := by
  have k : Ledger.Holds (hotAt P.toOwnPar Y ιN) y := by
    unfold hotAt
    exact (ledOf_holds _ y).2 h
  exact k

/-- The part stack. -/
theorem stackF_holds
    (h1 : Blocks.Form.val y (upForm (J₂ := J₂) (Cb.Sub.formU P.ip.inn.toSum.T.par
      (fun _ b _ _ => PEmpty.elim b) ((tailW P).b4 e).2)) = 0)
    (h2 : Blocks.Form.val y (rowF P.ip (J₂ := J₂) ((tailW P).b4 e).2 (.inl (.inl ()))) = 0)
    (h3 : Blocks.Form.val y (rowF P.ip (J₂ := J₂) ((tailW P).b4 e).2 (.inr (.inl ()))) = 0) :
    Ledger.Holds (clFirst P Y ιN ιT ιG ιE R zt b B sG e).stack y := by
  have k : Ledger.Holds (stackLed (J₂ := J₂) P.ip ((tailW P).b4 e).2) y := by
    unfold stackLed
    refine (ledOf_holds _ y).2 fun f hf => ?_
    simp only [stackCl, List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl
    · exact h1
    · exact h2
    · exact h3
  exact k

/-- The part emb. -/
theorem embF_holds (h : Blocks.Form.val y (embClaim Y ιE (((tailW P).y7 e).1.2 (0 : Fin 1)) P.mkE
      P.nb P.gB (stF P e).pb) = 0) :
    Ledger.Holds (clFirst P Y ιN ιT ιG ιE R zt b B sG e).emb y := by
  have k : Ledger.Holds (embLedOf Y ιE (((tailW P).y7 e).1.2 (0 : Fin 1)) P.mkE P.nb P.gB
      (stF P e).pb) y := by
    unfold embLedOf
    refine (ledOf_holds _ y).2 fun f hf => ?_
    rw [List.mem_singleton] at hf
    rw [hf]
    exact h
  exact k

/-- **Eight parts of the first group's ledger, where the claims of the run "front" are worth 0.** -/
theorem parts_of_claims_first {ρ : Reading E} {W : World E} {Pp : Pub} {o : Own}
    (Dc : FrontDict ρ W Pp o P.D (namesAt P.ofp.nr (readsAt Y ιN))
      (eAtF P.ofp P.wfPart e (zt e)) (namesT P.tp (readsT Y ιT))
      (termsEAt P.tp ((tailW P).b3 e).2) (gNamesAt P.fp (gReadsAt Y ιG))
      (gatedEAt P.fp ((tailW P).b5 e).2 ((tailW P).b6 e).2) b B sG y)
    {g : ℕ} {rows : Bool} {F G : Fork} {fs : Array OnBytes.Model.Aff} (hp : o.v.y.h.p3 = true)
    {o2 : Level} (h2 : o.hd2 = some o2)
    (h : Desc.First.K4.formsFrontWith rows Pp g o F = some (fs, G))
    (hz : ∀ f ∈ fs.toList, f.value ρ W = 0)
    (u1 : Blocks.Form.val y (u1At P.ofp.nr ((tailW P).b1 e).2) = 0)
    (u2 : Blocks.Form.val y (u2At P.ofp.nr ((tailW P).b2 e).2) = 0)
    (u5 : Blocks.Form.val y (prodU P.fp.gp ((tailW P).b5 e).2) = 0)
    (u6 : Blocks.Form.val y (prodU P.fp.rt.L ((tailW P).b6 e).2) = 0)
    (u4 : Blocks.Form.val y (upForm (J₂ := J₂) (Cb.Sub.formU P.ip.inn.toSum.T.par
      (fun _ b _ _ => PEmpty.elim b) ((tailW P).b4 e).2)) = 0)
    (rA : Blocks.Form.val y (rowF P.ip (J₂ := J₂) ((tailW P).b4 e).2 (.inl (.inl ()))) = 0)
    (rB : Blocks.Form.val y (rowF P.ip (J₂ := J₂) ((tailW P).b4 e).2 (.inr (.inl ()))) = 0)
    (uE : Blocks.Form.val y (embClaim Y ιE (((tailW P).y7 e).1.2 (0 : Fin 1)) P.mkE P.nb P.gB
      (stF P e).pb) = 0) :
    Ledger.Holds (clFirst P Y ιN ιT ιG ιE R zt b B sG e).sq y ∧
      Ledger.Holds (clFirst P Y ιN ιT ιG ιE R zt b B sG e).bat y ∧
      Ledger.Holds (clFirst P Y ιN ιT ιG ιE R zt b B sG e).led y ∧
      Ledger.Holds (clFirst P Y ιN ιT ιG ιE R zt b B sG e).terms y ∧
      Ledger.Holds (clFirst P Y ιN ιT ιG ιE R zt b B sG e).gated y ∧
      Ledger.Holds (clFirst P Y ιN ιT ιG ιE R zt b B sG e).hot y ∧
      Ledger.Holds (clFirst P Y ιN ιT ιG ιE R zt b B sG e).stack y ∧
      Ledger.Holds (clFirst P Y ιN ιT ιG ιE R zt b B sG e).emb y :=
  have v := values_of_front Dc hp h2 h hz 0
  ⟨sqF_holds P Y ιN ιT ιG ιE R zt b B sG e y u1 v.1 v.2.1,
    batF_holds P Y ιN ιT ιG ιE R zt b B sG e y v.2.2.1,
    ledF_holds P Y ιN ιT ιG ιE R zt b B sG e y u2 0 v.2.2.2.1,
    termsF_holds P Y ιN ιT ιG ιE R zt b B sG e y v.2.2.2.2.1,
    gatedF_holds P Y ιN ιT ιG ιE R zt b B sG e y u5 u6 v.2.2.2.2.2.1,
    hotF_holds P Y ιN ιT ιG ιE R zt b B sG e y v.2.2.2.2.2.2,
    stackF_holds P Y ιN ιT ιG ιE R zt b B sG e y u4 rA rB,
    embF_holds P Y ιN ιT ιG ιE R zt b B sG e y uE⟩

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.parts_of_claims_first
