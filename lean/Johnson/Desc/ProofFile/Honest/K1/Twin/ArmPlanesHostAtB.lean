-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/Twin/ArmPlanesHostAtB.lean: MADE BY PROGRAM OFF
Johnson/Desc/K1/Law/ArmPlanesHostAt.lean UNDER A MAP OF NAMES AND ONE TURN OF THE MEANING:
3 OF ITS DECLARATIONS: there_at342_b · planesLeft5_at342_b · planesLeft4_at342_b. THE PROOFS ARE
COPIES.

This letter is for the honest run's own forms alone: no statement on any other party may take it.
NEVER ON SOUNDNESS's ROAD: at the meaning "honest" the
clauses noColl, shown and decodes are True by definition: a law at that meaning may stand beneath
statements on completeness or zero knowledge only, never beneath a statement on soundness.

The map of names. ReadsFence to ReadsFenceB; each twinned theorem n to n_b; the library's closed
facts at its wider table of names (mwMore) to their likes at mgMore, and its laws on the wider
meaning to their likes on "honest" over mgAll (both in Twin/HonestAt.lean, typed by hand).
The turn of the meaning. Where the elder has the wider meaning (mw1 Dm.N (d13 Dm) dk (mgAll Dm Mg₀),
or plus13 (d13 Dm) dk (mgAll Dm Mg₀)), the twin has honest (mgAll Dm Mg₀) ans test
(Johnson/Desc/ProofFile/Honest/Thread/First.lean): the meaning at which the honest thread's own
promise stands; at the item "tie": mgAll Dm Mg₀. The step down from mw1 to plus13 (inAt_down) falls.
The promise itself is the library's InAt: no new text of a promise.
Laid in, on no line of a statement: the letters ans and test, behind each block of letters: implicit
in the theorems, explicit in the structure ReadsFenceB; "include dk" where the source's block
binds dk (no twin's statement names it; it is kept so that a copied call has the source's number
of arguments). Kept as they stand in the source: its namespace, open, variable, section, set_option
and attribute lines, but for one prefix that makes dk implicit (in ArmAtReadsB.lean): there "omit dk
in" stands.
The namespace is the library's, so that a copied proof finds its callees without a sign turned; the
names with the suffix _b are not the library's.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.K1.Law.ArmPlanesHostAt
import Johnson.Desc.ProofFile.Honest.K1.Twin.ArmAtReadsB
import Johnson.Desc.ProofFile.Honest.K1.Twin.ArmHeadPromiseB
import Johnson.Desc.ProofFile.Honest.K1.Twin.ArmPlanesLenB
import Johnson.Desc.ProofFile.Honest.K1.Twin.HonestAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.K1

open ProofFile.Honest.FirstThread (honest)
open VerifiableInference.Desc (Strs Wit)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound (CellsQ MsgT mgMore)
open OnBytes OnBytes.Params OnBytes.Model
open VerifiableInference.Desc (Block Chain FileDescription Strs)
open VerifiableInference.Desc.First (S HeadOwn Numbers flatPlacesOf)
open VerifiableInference.Desc.Sound (linksFull MsgT MgData CellsQ mgAll d13 mgBase seatTab dataQ
  cellsAt)
open VerifiableInference.Desc.K12.Door (K12Data)
open VerifiableInference.Desc.Kinds.Head.Law (withTables withTables_iff p8K6 readsOf TablesCome
  MatsSeated cell_wider k6_NM)
open OnBytes.Params (Rounds)
open ProofFile (Cl)

section
variable {Xi Tok : Type} {rows cols nR : ℕ} {XV : OnBytes.Model.Verify.Public}
  (Dm : MgData Xi ProofFile.InstPub Tok rows cols nR XV) (dk : K12Data)

variable {ans : ℕ → ℕ → ProofFile.InstPub × S → Strs → Wit (CellsQ rows cols) Tok MsgT → Prop} {test : ℕ → S → Option String}
include dk
/-- The ledger in front has an array wherever the written list has one. -/
theorem there_at342_b (i : ℕ) (hT : ∃ t, (Dm.pubD.dS.trees 24)[i]? = some t)
    {x : ProofFile.InstPub × S} {y : Strs}
    (hIn : InAt Dm.N (honest (mgAll Dm mgBase) ans test) linksFull
      (flatPlacesOf linksFull true) (noL 24 false) x y) (P : K8.ReadsQuiet.PH) :
    ∀ e F, withTables P x.2 = some e → e.fork? = some F → ∃ tr, F.trees[i]? = some tr := by
  intro e F he hF
  obtain ⟨a, cov, xx, tt, ha, hop, _, _, _, rfl⟩ := (withTables_iff P x.2 e).1 he
  have e1 : ({ x.2 with here := .head { a with t := some tt } } : S).fork? = x.2.fork? := by
    unfold S.fork?
    rw [ha]
  rw [e1] at hF
  have h0 := pub_at342_b Dm dk (.more (some 24) "ledger.treesAre")
    (Bool.and_eq_true_iff.1 open342_mg).2 hIn
  rw [First.pubAll_more_treesAre] at h0
  unfold First.FillSent.treesAreB at h0
  rw [hF] at h0
  have h1 : F.trees.toList.map First.FillSent.treeLook = Dm.pubD.dS.trees 24 := by
    simpa using h0
  obtain ⟨t, ht⟩ := hT
  rw [← h1, List.getElem?_map, Array.getElem?_toList] at ht
  obtain ⟨tr, htr, _⟩ := Option.map_eq_some_iff.1 ht
  exact ⟨tr, htr⟩

end

section
variable {Xi Tok : Type} {rows cols nR : ℕ} {XV : OnBytes.Model.Verify.Public}
  {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A₀ : ProofFile.SharedSeat} {B₀ : ProofFile.SecondSeat}

variable {ans : ℕ → ℕ → ProofFile.InstPub × S → Strs → Wit (CellsQ rows cols) Tok MsgT → Prop} {test : ℕ → S → Option String}
/-- **hHostC inside the fence.** -/
theorem planesLeft5_at342_b (Dm : MgData Xi ProofFile.InstPub Tok rows cols nR XV) (dk : K12Data)
    (J : S → Prop) (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A₀ B₀)
    (hWX : Bs.G₀.W = XV) (aN : ℕ) (R₁ R₂ R₃ : Rounds) (cU : ℕ × String) (num6 : ℕ → ℕ → ℕ)
    (lay6 : ReqLayout)
    (T : _root_.Meaning.laidThere XV (_root_.Meaning.sizesOf XV) lay6 = true)
    (hU : (Dm.pubD.d3.arrayOf.getD 24 #[])[readsOf XV]? = some cU)
    (hK : ∀ t, (Dm.pubD.dS.trees 24)[readsOf XV]? = some t → XV.H.nU.getD 2 0 ≤ t.2.1)
    (hTh : ∃ t, (Dm.pubD.dS.trees 24)[readsOf XV]? = some t)
    (hShape : ∀ p h, First.Look.placeAt XV 24 false = some p → p.shape = some h →
      h = XV.HLy.fs)
    (hLabP : (Dm.pubD.d3.arrayOf.getD 24 #[])[XV.H.tl.gtTree.getD (XV.hS.NHf + 2) 0]? =
      some (_root_.Meaning.ownerK (_root_.Meaning.labAt XV 24 (XV.hS.NHf + 2)),
        _root_.Meaning.nameOf
          (_root_.Meaning.ownerA (_root_.Meaning.labAt XV 24 (XV.hS.NHf + 2)))))
    {X : Stages.LinkH} {arrs : Option (List ℕ)} {x x' : ProofFile.InstPub × S} {y y' : Strs}
    {w : Wit (CellsQ rows cols) Tok MsgT} {p : ℕ × String} {A B : K9.Part}
    (Fc : ReadsFenceB Dm mgBase ans test J Z Bs aN R₁ R₂ R₃ c 24 X arrs x x' y y' w p A B)
    (L : PlanesLeft6 XV (Dm.N.sent 24 0) x.2 A Dm.arr Dm.N num6 lay6) :
    PlanesLeft5 XV (Dm.N.sent 24 0) (Dm.N.group 24) x.2 A B (seatTab Dm.cs Dm.arr Dm.ms w) := by
  have hr := rides_at_reads_b Fc
  have hTC : TablesCome XV x.2 x'.2 := by
    obtain ⟨_, rs, gs, hfit, hd⟩ := Fc.yes
    have hlen : (rs.map noDigest).length = 2 := by
      rw [List.length_map, Keeps.fit_length _ _ hfit, rounds_blkL]
    rw [← hWX]
    exact tablesCome_at_reads Z Bs.G₀ X Fc.built _ arrs x.2 x'.2 _ gs hlen hd
  have eA := arrays_at342_b Dm dk Fc.inAt Fc.front
  obtain ⟨p0, h0, hp0, hs0, hg0⟩ := shape_at342_b Dm dk Fc.inAt
  exact planesLeft5_of_tie (hWX ▸ O.public) _ _ x.2 x'.2 A B _ hr.arrays
    (wide_at342_b Dm dk _ _ hK Fc.inAt _) (there_at342_b Dm dk _ hTh Fc.inAt _) hTC
    (cellsAt Dm.cs Dm.arr Dm.ms Dm.N 24 (x'.1, x'.2)) w Fc.tie
    (fun t c r i hc => Sound.cellsAt_name Dm.cs Dm.arr Dm.ms Dm.N 24 x'.1 x'.2 w B Fc.behind t c hc
      r i)
    cU (by rw [eA]; exact hU) (heard_of_look L.hlk)
    (fun gk hgk => (hg0 gk hgk).trans (hShape p0 h0 hp0 hs0)) (by rw [eA]; exact hLabP)
    (fun c i' hc hi => ride_at (fun μ _ => μ = XV.hS.NHf + 2) XV _ _ A B _
      (fun _ hx => List.mem_append_left _ (List.mem_append_left _ hx)) hr Dm.arr Dm.N num6 lay6 T
      L.hlay L.hMatsP _ c i' (by rw [k6_NM (hWX ▸ O.public)]; omega) hc hi rfl)

/-- **PlanesLeft4 inside the fence**: the end of the premise hPl'. -/
theorem planesLeft4_at342_b (Dm : MgData Xi ProofFile.InstPub Tok rows cols nR XV) (dk : K12Data)
    (J : S → Prop) (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A₀ B₀)
    (hWX : Bs.G₀.W = XV) (aN : ℕ) (R₁ R₂ R₃ : Rounds) (cU : ℕ × String) (num6 : ℕ → ℕ → ℕ)
    (lay6 : ReqLayout)
    (T : _root_.Meaning.laidThere XV (_root_.Meaning.sizesOf XV) lay6 = true)
    (hU : (Dm.pubD.d3.arrayOf.getD 24 #[])[readsOf XV]? = some cU)
    (hK : ∀ t, (Dm.pubD.dS.trees 24)[readsOf XV]? = some t → XV.H.nU.getD 2 0 ≤ t.2.1)
    (hTh : ∃ t, (Dm.pubD.dS.trees 24)[readsOf XV]? = some t)
    (hShape : ∀ p h, First.Look.placeAt XV 24 false = some p → p.shape = some h →
      h = XV.HLy.fs)
    (hLabP : (Dm.pubD.d3.arrayOf.getD 24 #[])[XV.H.tl.gtTree.getD (XV.hS.NHf + 2) 0]? =
      some (_root_.Meaning.ownerK (_root_.Meaning.labAt XV 24 (XV.hS.NHf + 2)),
        _root_.Meaning.nameOf
          (_root_.Meaning.ownerA (_root_.Meaning.labAt XV 24 (XV.hS.NHf + 2)))))
    (hLen : ∀ p h, First.Look.placeAt XV 24 false = some p → p.shape = some h →
      h.NC * 2 ^ (h.kT + 5 - (p8K6 XV 24).h.lmbH) ≤
        ((p8K6 XV 24).hp.tl.mats.getD ((p8K6 XV 24).h.NHf + 1 + 1) {}).k *
          (((p8K6 XV 24).hp.tl.mats.getD ((p8K6 XV 24).h.NHf + 1 + 1) {}).m /
            2 ^ (p8K6 XV 24).h.lmbH))
    {X : Stages.LinkH} {arrs : Option (List ℕ)} {x x' : ProofFile.InstPub × S} {y y' : Strs}
    {w : Wit (CellsQ rows cols) Tok MsgT} {p : ℕ × String} {A B : K9.Part}
    (Fc : ReadsFenceB Dm mgBase ans test J Z Bs aN R₁ R₂ R₃ c 24 X arrs x x' y y' w p A B)
    (L : PlanesLeft6 XV (Dm.N.sent 24 0) x.2 A Dm.arr Dm.N num6 lay6) :
    PlanesLeft4 XV (Dm.N.sent 24 0) (Dm.N.group 24) x.2 A B (seatTab Dm.cs Dm.arr Dm.ms w) :=
  planesLeft4_of_b Dm dk hLen Fc.inAt
    (planesLeft5_at342_b Dm dk J O hWX aN R₁ R₂ R₃ cU num6 lay6 T hU hK hTh hShape hLabP Fc L)

end

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.there_at342_b
#print axioms VerifiableInference.Desc.K1.planesLeft5_at342_b
#print axioms VerifiableInference.Desc.K1.planesLeft4_at342_b
