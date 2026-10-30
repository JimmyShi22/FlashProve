-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/EntryRec/RecLaws.lean: what the forms of Johnson/EntryRec/RecDefs.lean are, and what the
library's theorem on the compiled verifier with the record gives at the object `LrX`.

The equations. No hypothesis; for every family g of typed oracle functions.
  `vlco_eq`: `VLCO` is the run of Johnson/RecCompile/Cms.lean's `vLC`, its term untouched, at the
    wiring `WrX` and at the typed string made of π and the tables. Four steps, each a theorem that
    lay already: `verifyPLO_eq`, `verifyPL_pieces`, the library's `thin_reads`, and
    OnBytes/Slice/TopAny.lean's `verifyBS_ann`. The last is needed because the skeleton's marking
    `Twin.allLo` equals the library's `RoundSplits.allLocal` by a theorem and not by unfolding: so `vLC`'s
    string is `reAnn _ π` (the same eight fields) and its wiring is `wireTo` of the skeleton's.
  `seedIsO_eq`: `seedIsO` is the run of `seedIs`.
  `vceo_eq`: `VCEO` is the run of `VCE`.
For every object with records, wiring and wire of the record.
  `VCE`: the terms that `VC`'s text has for the two seeds and for Link, in `VC`'s order, and their
    conjunction. `seedIs_det`, `vce_det`: their runs.
  `vc_vce`: a yes of `VC` is a yes of `VCE`, at the key's root and record and the link that the
    proof names.
What the library's theorem asks, paid from what is known of `skeletonOverBothExternalStrings`.
  `psofR_local`; `psofR_sound` (soundness with the records as the instance is soundness record by
  record, with one list of counts); `wqR_okg`, `wq0_okg`, `okc_WrX` (the laws of the wires, `OKC`);
  `sndT_LrX`, `sndB_LrX` (what accepts nothing is sound).
  `entry_bcs`: Johnson/RecCompile/CmsBcs.lean's `cms_bcs` at `LrX` and `WrX`. Its hypotheses, each
    named: `noneColl` (a collision at a record's seed makes the decoder give none); `rcd` (a word
    has at most eR collision seeds); `sndL` (for every pair of records, `skeletonOverBothExternalStrings` at `dec rr` is
    round-by-round sound for "the first word does not decode at the first record, or the second word
    has a collision at the second record's seed, or both decode to one index", with one list of
    counts εL); `law` (the seed of K + 1 uniform blocks is a collision seed with probability at most
    εs); `belowL` (εL's counts lie below εs); `hown`, `h0` (own trees' numbers; the laws of the
    wiring of the description's rounds); `hS` (the laws of the record's wire, `OutOfDomainSampleQueryLayout.OK`).
  `seedW_exists`: a wire of the record with its two laws exists at `LrX` (the library's
    `exists_seedW`): the three shapes are not empty.

Limits.
  `entry_bcs`'s conclusion `BcsAtC` has clauses on Test and on a session: at `LrX` these accept
  nothing, so the two clauses are empty. Its clauses on a seed's query and on an accepted Link
  string are not. It speaks of `vLC'`, the Link verifier without the strict format's test, and of
  random typed oracles and traces; the equations above speak of `vLC` and of one family g. Nothing
  here joins the two.
  `cms_binding_lang` is not taken at `LrX`: it speaks of schemes whose verifier is `VC`, and `VC`
  accepts nothing there (RecDefs.lean's head).
  No hypothesis of `entry_bcs` is shown here of any decision, decoder or sampler. `seedW_exists`'s
  sampler is the library's (blocks modulo the number of seeds), not a program's.
  Nothing is said on completeness, and nothing can be: the honest sides are placeholders.
  Used outside this file and RecDefs.lean: `psofR_up`, `psofR_local`, `psofR_sound`, `wqR_okg`,
  `VCE`, `vce_det`. No caller outside this file of anything that stands at `LrX` (`vceo_eq`,
  `entry_bcs` and `seedW_exists` have no caller at all), nor of `vc_vce`, which
  Johnson/EntryRec/Core.lean [not in this library]'s equation overtakes. What stands at `LrX`, and
    `VCE`, `vce_det` and
  `vc_vce`, are typed at the first form of the compiled verifier with the record (RecDefs.lean's
  head).

-/
import Johnson.EntryRec.RecDefs
import OnBytes.RunA.ListedOwnLaws
import OnBytes.Slice.TopAny
import Johnson.RecCompile.Wire
import Johnson.RecCompile.CmsBcs
import Johnson.RecCompile.SeedBS

set_option autoImplicit false

namespace OnBytes.RunA

open _root_.Run _root_.Run.PQ _root_.Run.Thin _root_.Run.Twin Iop Rom Compile Compile.Batch
open Compile.Batch.Cms OnBytes.Slice

/-- The protocol of the skeleton carries the marking "all rounds local". -/
theorem psofR_up (R : Type) (C : CK) (ds : List RD) (a : ℕ) (xs : List XO)
    (dec : R × R → View → Bool) :
    (PSofR R C ds a xs dec).up = BatchInteractiveOracleProof.ofProto (PSofR R C ds a xs dec).up.loc :=
  congrArg (BatchInteractiveOracleProof.mk (PSofR R C ds a xs dec).up.loc) (Twin.allLo_eq (SOf C ds))

theorem ps0_up (Y : Type) (C : CK) (n : ℕ) :
    (PS0 Y C n).up = BatchInteractiveOracleProof.ofProto (PS0 Y C n).up.loc :=
  congrArg (BatchInteractiveOracleProof.mk (PS0 Y C n).up.loc) (Twin.allLo_eq [s0 C])

section
variable {I RI Seed Ans : Type} [Fintype RI] [Nonempty RI] [Fintype Seed] [Nonempty Seed]
variable (X : Type) (C : CK) (K : Nat) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k) (ds : List RD)
  (a : Nat) (xs : List XO) (dec : (Seed × Ans) × (Seed × Ans) → View → Bool)
  (enc : I → RI → Fin (2 ^ a) → SgX) (ans : I → RI → Seed → Ans)
  (coll : (Fin (2 ^ a) → SgX) → Seed → Prop) (dcd : (Fin (2 ^ a) → SgX) → Seed × Ans → Option I)

/-- The map on plain parts is the carrying along the equation between the two markings. -/
theorem embPR_eq (z : PlainPart (Twin.up (SOf C ds)) (Twin.allLo (SOf C ds))) :
    embPR X C ds a xs dec enc ans coll dcd z = pbTo (Twin.allLo_eq (SOf C ds)) z := by
  cases z with
  | inl x => exact (pbTo_inl _ (Twin.allLo_eq (SL C ds)) _ x).symm
  | inr q =>
    exact (congrArg Sum.inr (embPL_eq C ds q)).trans
      (pbTo_inr _ (Twin.allLo_eq (SL C ds)) _ q).symm

/-- The wiring of the protocol that accepts nothing. -/
def wq0 (Y : Type) : ProtocolQueryLayout 256 (K + 1) (PS0 Y C (2 ^ a)).up :=
  ⟨(wire0S C K chal, ()), WireE.one (2 ^ a) SgX (0, []),
    inferInstanceAs (DecidableEq (Empty ⊕ Empty)), 0, a⟩

/-- **The whole wiring** (Johnson/RecCompile/Wire.lean, `wireOf`): Link's is the protocol's; Test
and the session have one idle round each. -/
noncomputable def WrX : QueryLayout 256 (LrX X C ds a xs dec enc ans coll dcd).carrierC :=
  wireOf (L := LrX X C ds a xs dec enc ans coll dcd) (K + 1)
    (wireTo (ps0_up _ C (2 ^ a)) (wq0 C K chal a _))
    (wireTo (psofR_up _ C ds a xs dec) (wqR _ C K chal ds a xs dec))
    (wireTo (ps0_up _ C (2 ^ a)) (wq0 C K chal a _)) a 0

/-- **What runs is the run of the compiled Link verifier with the two records**
(Johnson/RecCompile/Cms.lean, `vLC`), at every family of typed oracle functions, at the typed string
made of π and the tables. No hypothesis. -/
theorem vlco_eq (g : Fam (spec 256 (K + 1) (LrX X C ds a xs dec enc ans coll dcd).carrierC))
    (p : Params) (cfg : ByteArray) (cm cm' : Dig 256) (rec rec' : Seed × Ans)
    (π : OneProtocolProof 256 (PSofR (Seed × Ans) C ds a xs dec).up)
    (otabs : List (Nat × List (Nat × Row3)))
    (tabs : List (Bool × OpenB × List (List (Dig 256)))) :
    VLCO X C K chal ds a xs dec enc ans coll dcd g p.sMT p.sFS cfg cm cm' rec rec' π otabs tabs =
      (vLC (WrX X C K chal ds a xs dec enc ans coll dcd) p cm cm' rec rec'
        (reAnn _ { π with
          opens := opensOfX 0 C ds a xs (fun _ => true) otabs
          ext := extOf a cfg tabs })).det g := by
  unfold VLCO
  have hw : ((wire0Less C K chal, wiresLessSL C K chal ds) : WireSLess 256 (K + 1) (SOf C ds)) =
      lessS (SOf C ds) (Twin.allLo (SOf C ds)) (wire0S C K chal, wiresSL C K chal ds)
        (((fun _ => [], fun _ => []), leavesSL C ds) : LeavesS (SOf C ds)) := by
    show _ = (lessR (wire0S C K chal) ((fun _ => [], fun _ => [])),
      lessS (SL C ds) (Twin.allLo (SL C ds)) (wiresSL C K chal ds) (leavesSL C ds))
    rw [lessS_SL]
    rfl
  rw [hw]
  refine (verifyPLO_eq (fun _ => (LrX X C ds a xs dec enc ans coll dcd).carrierC) g
    (readsInOrder2 (2 ^ a)) (fun z => (z.1.map id, z.2)) none p.sMT p.sFS .link
    (PSofR (Seed × Ans) C ds a xs dec) (wire0S C K chal, wiresSL C K chal ds)
    (((fun _ => [], fun _ => []), leavesSL C ds) : LeavesS (SOf C ds))
    (decOS C ds) (weLessX a) (nOpen ds + (xs.map (·.count)).sum) (max (maxDepth ds) a)
    (fun p s => some (.inr ⟨Tag.link, ⟨p, s⟩⟩)) (embPR X C ds a xs dec enc ans coll dcd)
    (fun rr => some (none, rr.1, rr.2)) (fun s => some (.inl s)) 0 [cm, cm'] (rec, rec')
    { π with
      opens := opensOfX 0 C ds a xs (fun _ => true) otabs
      ext := extOf a cfg tabs }
    (listedX a tabs) (ownListedX ds otabs)
    ⟨fun _ _ _ => ⟨rfl, rfl⟩, leaves_SL C K chal ds⟩
    ⟨fun _ p _ _ => p.elim, fun _ p _ _ => p.elim, listed_SL C K chal otabs ds⟩).trans ?_
  refine (verifyPL_pieces (fun _ => (LrX X C ds a xs dec enc ans coll dcd).carrierC) g
    (readsInOrder2 (2 ^ a)) (fun z => (z.1.map id, z.2)) none p.sMT p.sFS .link
    (PSofR (Seed × Ans) C ds a xs dec) (wqR _ C K chal ds a xs dec)
    (wire0S C K chal, wiresSL C K chal ds) (decOS C ds) (weLessX a)
    (nOpen ds + (xs.map (·.count)).sum) (max (maxDepth ds) a)
    (fun p s => some (.inr ⟨Tag.link, ⟨p, s⟩⟩)) (embPR X C ds a xs dec enc ans coll dcd)
    (fun rr => some (none, rr.1, rr.2)) (fun s => some (.inl s)) 0 [cm, cm'] (rec, rec')
    { π with
      opens := opensOfX 0 C ds a xs (fun _ => true) otabs
      ext := extOf a cfg tabs }
    (listedX a tabs) rfl rfl rfl rfl rfl
    (order2 (2 ^ a) SgX (0, [])) (extOf_listed a cfg tabs)
    (all2_complete (2 ^ a) SgX (0, []))).trans ?_
  refine (thin_reads I _ 256 (K + 1) (LrX X C ds a xs dec enc ans coll dcd).carrierC g _ _
    p.sMT p.sFS .link (PSofR (Seed × Ans) C ds a xs dec) (wqR _ C K chal ds a xs dec)
    (fun p s => some (.inr ⟨Tag.link, ⟨p, s⟩⟩)) (embPR X C ds a xs dec enc ans coll dcd)
    (fun rr => some (none, rr.1, rr.2)) (fun s => some (.inl s)) 0 [cm, cm'] (rec, rec')
    { π with
      opens := opensOfX 0 C ds a xs (fun _ => true) otabs
      ext := extOf a cfg tabs }).trans ?_
  exact congrArg (fun c => OComp.det g c)
    (verifyBS_ann (lam := 256) (K := K + 1) (L := (LrX X C ds a xs dec enc ans coll dcd).carrierC)
      p.sMT p.sFS .link (PSofR (Seed × Ans) C ds a xs dec).up.loc
      (Twin.allLo (SOf C ds)) (RoundSplits.allLocal (Twin.up (SOf C ds))) (Twin.allLo_eq (SOf C ds))
      (wqR _ C K chal ds a xs dec) (fun p s => some (.inr ⟨Tag.link, ⟨p, s⟩⟩))
      (embPR X C ds a xs dec enc ans coll dcd) id (embPR_eq X C ds a xs dec enc ans coll dcd)
      (fun rr => some (none, rr.1, rr.2)) (fun s => some (.inl s)) 0 [cm, cm'] (rec, rec')
      { π with
        opens := opensOfX 0 C ds a xs (fun _ => true) otabs
        ext := extOf a cfg tabs })

end

/-! ### The entry's share of the compiled verifier with the record, for every object -/

section
variable {I X : Type} {lam : ℕ} {L : HolographicProtocol I X} (W : QueryLayout lam L.carrierC) (S : OutOfDomainSampleQueryLayout lam W.K L)

/-- **The entry's share of `VC`**: the terms that `VC`'s text has for the two seeds and for Link, in
`VC`'s order, and their conjunction. -/
noncomputable def VCE (p : Params) (cm cmj : Dig lam) (rcd recj : L.Rec)
    (πL : OneProtocolProof lam (BatchInteractiveOracleProof.ofProto L.link)) : TypedOracleComputation lam W.K L.carrierC Bool :=
  (seedIs W S S.t0 cm rcd.1).bind fun s0 =>
  (seedIs W S S.t1 cmj recj.1).bind fun sj =>
  (vLC W p cm cmj rcd recj πL).bind fun b =>
  OComp.pure (s0 && sj && b)

/-- `decide` says yes if and only if the proposition holds, whatever the instance. -/
theorem decide_iff_of {q : Prop} (i : Decidable q) : @decide q i = true ↔ q :=
  @decide_eq_true_iff q i

/-- The run of one seed's query says yes if and only if the seed of the oracle's answer is s. -/
theorem seedIs_det (g : Fam (spec lam W.K L.carrierC)) (t : Tag) (cm : Dig lam) (s : L.OutOfDomainSeed) :
    (seedIs W S t cm s).det g = true ↔
      S.seed (show FsAns lam W.K from g (OracleName.fb t) (seedQ W S t cm)).1 = s := by
  unfold seedIs
  rw [OComp.det_bind]
  exact decide_iff_of _

/-- The run of the entry's share is the conjunction of the three runs. -/
theorem vce_det (g : Fam (spec lam W.K L.carrierC)) (p : Params) (cm cmj : Dig lam)
    (rcd recj : L.Rec) (πL : OneProtocolProof lam (BatchInteractiveOracleProof.ofProto L.link)) :
    (VCE W S p cm cmj rcd recj πL).det g =
      ((seedIs W S S.t0 cm rcd.1).det g && (seedIs W S S.t1 cmj recj.1).det g &&
        (vLC W p cm cmj rcd recj πL).det g) := by
  unfold VCE
  simp only [OComp.det_bind, OComp.det]

/-- **A yes of `VC` is a yes of its entry's share**, at the key's root and record and the link that
the proof names, under every family of oracle functions. -/
theorem vc_vce (g : Fam (spec lam W.K L.carrierC)) (p : Params) (v : FullKey lam L) (x : X)
    (π : RequestProof lam L) (h : (VC W S p v x π).det g = true) :
    ∃ cmj recj πL, v.links[π.leaf]? = some (cmj, recj, some πL) ∧
      (VCE W S p v.cm cmj v.rcd recj πL).det g = true := by
  unfold VC at h
  split at h
  · next πT cmj recj πL πB h1 h2 h3 =>
    refine ⟨cmj, recj, πL, h2, ?_⟩
    unfold VCE
    simp only [OComp.det_bind, OComp.det, Bool.and_eq_true] at h ⊢
    exact ⟨h.1.1.1, h.1.2⟩
  · simp [OComp.det] at h

end

section
variable {I RI Seed Ans : Type} [Fintype RI] [Nonempty RI] [Fintype Seed] [Nonempty Seed]
variable (X : Type) (C : CK) (K : Nat) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k) (ds : List RD)
  (a : Nat) (xs : List XO) (dec : (Seed × Ans) × (Seed × Ans) → View → Bool)
  (enc : I → RI → Fin (2 ^ a) → SgX) (ans : I → RI → Seed → Ans)
  (coll : (Fin (2 ^ a) → SgX) → Seed → Prop) (dcd : (Fin (2 ^ a) → SgX) → Seed × Ans → Option I)

/-- **One seed's query**: what runs is the run of `seedIs`. -/
theorem seedIsO_eq [DecidableEq Seed]
    (g : Fam (spec 256 (K + 1) (LrX X C ds a xs dec enc ans coll dcd).carrierC))
    (S : OutOfDomainSampleQueryLayout 256 (K + 1) (LrX X C ds a xs dec enc ans coll dcd)) (t : Tag) (cm : Dig 256)
    (s : Seed) :
    seedIsO X C K ds a xs dec enc ans coll dcd g t (S.pl t) S.seed cm s =
      (seedIs (WrX X C K chal ds a xs dec enc ans coll dcd) S t cm s).det g := by
  rw [Bool.eq_iff_iff]
  unfold seedIsO
  dsimp only
  exact decide_eq_true_iff.trans
    (seedIs_det (WrX X C K chal ds a xs dec enc ans coll dcd) S g t cm s).symm

/-- **What runs is the run of the entry's share of `VC`.** No hypothesis. -/
theorem vceo_eq [DecidableEq Seed]
    (g : Fam (spec 256 (K + 1) (LrX X C ds a xs dec enc ans coll dcd).carrierC))
    (S : OutOfDomainSampleQueryLayout 256 (K + 1) (LrX X C ds a xs dec enc ans coll dcd)) (p : Params) (cfg : ByteArray)
    (cm cm' : Dig 256) (rec rec' : Seed × Ans)
    (π : OneProtocolProof 256 (PSofR (Seed × Ans) C ds a xs dec).up)
    (otabs : List (Nat × List (Nat × Row3)))
    (tabs : List (Bool × OpenB × List (List (Dig 256)))) :
    VCEO X C K chal ds a xs dec enc ans coll dcd g S.t0 S.t1 S.pl S.seed p.sMT p.sFS cfg cm cm'
        rec rec' π otabs tabs =
      (VCE (WrX X C K chal ds a xs dec enc ans coll dcd) S p cm cm' rec rec'
        (reAnn _ { π with
          opens := opensOfX 0 C ds a xs (fun _ => true) otabs
          ext := extOf a cfg tabs })).det g := by
  unfold VCEO
  rw [seedIsO_eq X C K chal, seedIsO_eq X C K chal, vlco_eq]
  exact (vce_det (WrX X C K chal ds a xs dec enc ans coll dcd) S g p cm cm' rec rec' _).symm

/-! ### What the library's theorems ask of the object, from what is known of `skeletonOverBothExternalStrings` -/

/-- The decision depends on the oracles only at the positions read: from the same of `skeletonOverBothExternalStrings`, record
by record. -/
theorem psofR_local (R : Type) (dec : R × R → View → Bool) :
    (PSofR R C ds a xs dec).up.loc.IsLocal :=
  fun rr y y' τ τ' h1 h2 h3 h4 => psofX_local C ds a xs (dec rr) () y y' τ τ' h1 h2 h3 h4

/-- **Round-by-round soundness with the records as the instance is round-by-round soundness record
by record**, with one list of counts. -/
theorem psofR_sound (R : Type) (dec : R × R → View → Bool)
    (Lg : R × R → (twoExternalStrings (2 ^ a) SgX).Str → Prop) (ε : Err (Twin.up (SOf C ds))) :
    (PSofR R C ds a xs dec).up.loc.Sound Lg ε ↔
      ∀ rr, (skeletonOverBothExternalStrings C ds a xs (dec rr)).up.loc.Sound (fun _ y => Lg rr y) ε :=
  ⟨fun h rr _ y hn => h rr y hn, fun h rr y hn => h rr () y hn⟩

/-- The laws of Link's wiring: those of `wqX`. -/
theorem wqR_okg (R : Type) (dec : R × R → View → Bool) (dec₀ : View → Bool)
    (hown : ∀ d ∈ ds, ∀ n ∈ d.opens, n < 2 ^ 16) (h0 : (wqS C K chal ds dec₀).OKG) :
    (wqR R C K chal ds a xs dec).OKG :=
  have h := wqX_okg C K chal ds a xs dec₀ dec₀ hown h0
  ⟨h.sh, h.ext, fun _ ρ pl => h.opens () ρ pl, h.depth⟩

theorem wq0_okg (Y : Type) (dec₀ : View → Bool) (h0 : (wqS C K chal ds dec₀).OKG) :
    (wq0 C K chal a Y).OKG :=
  { sh := ⟨h0.sh.1, trivial⟩, ext := WireE.one_ok (2 ^ a) SgX (0, []),
    opens := fun _ _ _ => le_refl 0, depth := ⟨⟨Nat.zero_le _, Nat.zero_le _⟩, trivial⟩ }

/-- **The laws of the wires** that Johnson/RecCompile/Cms.lean asks (`OKC`). -/
theorem okc_WrX (S : OutOfDomainSampleQueryLayout 256 (K + 1) (LrX X C ds a xs dec enc ans coll dcd)) (dec₀ : View → Bool)
    (hown : ∀ d ∈ ds, ∀ n ∈ d.opens, n < 2 ^ 16) (h0 : (wqS C K chal ds dec₀).OKG) (hS : S.OK) :
    OKC (WrX X C K chal ds a xs dec enc ans coll dcd) S :=
  okc_wireOf (L := LrX X C ds a xs dec enc ans coll dcd) S
    (wireTo_okg _ _ (wq0_okg C K chal ds a _ dec₀ h0))
    (wireTo_okg _ _ (wqR_okg C K chal ds a xs _ dec dec₀ hown h0))
    (wireTo_okg _ _ (wq0_okg C K chal ds a _ dec₀ h0))
    (le_refl _) rfl
    ⟨by rw [wireTo_ext]; exact one_depth a, by rw [wireTo_ext]; rfl,
      by rw [wireTo_ext]; exact one_depth a⟩
    (by rw [wireTo_maxDepth]; exact le_refl _) (by rw [wireTo_maxDepth]; exact le_max_right _ _)
    (by rw [wireTo_maxDepth]; exact le_refl _)
    (fun _ => by rw [wireTo_ext]; exact ⟨rfl, rfl⟩) (fun _ => by rw [wireTo_ext]; exact ⟨rfl, rfl⟩)
    ⟨fun p => by rw [wireTo_ext]; exact ⟨rfl, rfl⟩, fun p => by rw [wireTo_ext]; exact ⟨rfl, rfl⟩⟩
    hS

/-- Test accepts nothing, so it is sound for every language, with the count 0. -/
theorem sndT_LrX (Lg : Seed × Ans → (oneExternalString (2 ^ a) SgX).Str → Prop) :
    (LrX X C ds a xs dec enc ans coll dcd).offline.Sound Lg (0, ()) :=
  fun _ _ _ _ => (Prob.cnt_false fun _ h => h rfl).le

/-- The session accepts nothing, so it has the library's soundness with a witness for every
relation and witness map, with the count 0. -/
theorem sndB_LrX {Wn : Type} (Rno : I → X → Wn → Prop)
    (wit : X × (Seed × Ans) → (oneExternalString (2 ^ a) SgX).Str → Tr (Twin.up [s0 C]) → Wn)
    (rec : Seed × Ans) :
    ((LrX X C ds a xs dec enc ans coll dcd).batAt rec).SndBKT 1 id none
      ((LrX X C ds a xs dec enc ans coll dcd).relB Rno rec) (fun x y τ => wit (x, rec) y τ)
      (0, ()) :=
  (sndBKT_laws _ _ _ _ _ _ _ _ _ _).2
    ⟨fun _ h => (by cases h), fun _ _ _ => false, fun _ _ => rfl, fun _ _ _ _ _ => rfl,
      fun _ _ _ h => (by cases h), fun _ _ _ _ h => (Bool.false_ne_true h).elim,
      fun _ x _ _ => ⟨fun j St hS _ => by
        obtain ⟨_, -, rfl⟩ := Option.map_eq_some_iff.1 hS
        exact (Prob.cnt_false fun _ h => Bool.false_ne_true h).le, fun _ => trivial⟩⟩

/-- **What the library proves of the compiled verifier with the record, at this object: every hole
a named hypothesis.** The conclusion is Johnson/RecCompile/Cms.lean's `BcsAtC`: outside a rare event
on traces, its clauses on a seed's query and on an accepted Link string. Its clauses on Test and on
a session are empty here: at this object they accept nothing. -/
theorem entry_bcs {Wn : Type} (S : OutOfDomainSampleQueryLayout 256 (K + 1) (LrX X C ds a xs dec enc ans coll dcd))
    (Rno : I → X → Wn → Prop)
    (wit : X × (Seed × Ans) → (oneExternalString (2 ^ a) SgX).Str → Tr (Twin.up [s0 C]) → Wn) (eR : ℕ)
    (εL : Err (Twin.up (SOf C ds))) (εs : ENNReal) (dec₀ : View → Bool)
    (noneColl : ∀ y (rec : Seed × Ans), coll y rec.1 → dcd y rec = none)
    (rcd : ∀ y, Prob.cnt (fun s => coll y s) ≤ eR)
    (sndL : ∀ rr : (Seed × Ans) × (Seed × Ans), (skeletonOverBothExternalStrings C ds a xs (dec rr)).up.loc.Sound
      (fun _ y => dcd y.1 rr.1 = none ∨ coll y.2 rr.2.1 ∨ dcd y.2 rr.2 = dcd y.1 rr.1) εL)
    (law : S.Law εs) (belowL : Err.Below εL εs)
    (hown : ∀ d ∈ ds, ∀ n ∈ d.opens, n < 2 ^ 16) (h0 : (wqS C K chal ds dec₀).OKG) (hS : S.OK) :
    BcsAtC (WrX X C K chal ds a xs dec enc ans coll dcd) S (fun i x => ∃ w, Rno i x w) εs :=
  cms_bcs I X Wn 256 (LrX X C ds a xs dec enc ans coll dcd)
    (WrX X C K chal ds a xs dec enc ans coll dcd) S Rno wit eR (0, ()) εL (0, ()) εs
    ⟨noneColl, rcd, sndT_LrX X C ds a xs dec enc ans coll dcd _,
      (psofR_sound C ds a xs _ dec _ εL).2 sndL, sndB_LrX X C ds a xs dec enc ans coll dcd Rno wit⟩
    law ⟨by simp, trivial⟩ belowL ⟨by simp, trivial⟩ rfl
    (fun _ _ _ _ _ _ _ _ _ => rfl) (psofR_local C ds a xs _ dec) (fun _ _ _ _ _ _ _ _ _ => rfl)
    (Iop.BatchOne.BAnn.allLocal_coherent _)
    (okc_WrX X C K chal ds a xs dec enc ans coll dcd S dec₀ hown h0 hS)

/-- The three shapes of the object are not empty, so the library's `exists_seedW` applies: a wire of
the record with its two laws exists at this object. -/
theorem seedW_exists [Countable (Seed × Ans)] (k e eR : ℕ) (c : ENNReal) (hk : k ≤ K + 1)
    (he : Fintype.card Seed * 2 ^ e ≤ 2 ^ (256 * k)) (rcd : ∀ y, Prob.cnt (fun s => coll y s) ≤ eR)
    (h : (eR : ENNReal) ≤ c * (Fintype.card Seed : ENNReal)) :
    ∃ S : OutOfDomainSampleQueryLayout 256 (K + 1) (LrX X C ds a xs dec enc ans coll dcd),
      S.OK ∧ S.Law ((1 + (2 ^ e : ENNReal)⁻¹) * c) :=
  exists_seedW (LrX X C ds a xs dec enc ans coll dcd) (List.cons_ne_nil _ _) (List.cons_ne_nil _ _)
    (List.cons_ne_nil _ _) (K + 1) k e eR c hk he rcd h

end

end OnBytes.RunA
