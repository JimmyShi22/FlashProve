-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/EntryRec/Laws.lean: what the form of Johnson/EntryRec/Defs.lean is, and what the library's
theorem on the compiled verifier with the record gives, at every object with records `LrG T` whose
Link has the shape, marks and reads of a description with two stored tables.

`hacc`, a hypothesis of the theorems below: Link's decision is the decision of the skeleton `PSofR`
at dec.

  `wLG`, `WrG`: Link's wiring (the skeleton's, its five fields), and the whole wiring
    (Johnson/RecCompile/Wire.lean, `wireOf`) from it and any wirings of Test and of the session with
    the same number of blocks; the depth of the tree over a word is a; the depth of the request tree
    is an argument.
  `vlcg_eq`: under `hacc`, for every family g of typed oracle functions, `VLCG` is the run of `vLC`,
    its term untouched, at `WrG` and the typed string made of π and the tables.
  `wLG_okg`, `okc_WrG`: the laws of the wires (`OKC`): Link's part is paid from the laws of the
    wiring of the description's rounds; of the two other wirings their own laws are asked, each
    named.
  `bcsG`: Johnson/RecCompile/CmsBcs.lean's `cms_bcs` at `LrG T` and `WrG`. Link's soundness is asked
    record by record at `skeletonOverBothExternalStrings` (`psofR_sound`); Link's locality is paid (`psofR_local`); what is
    asked of Test and of the session is the library's own, each named.

Limits. No hypothesis of `bcsG` is shown here of any object. One number K + 1 of blocks for all
three wirings, one word length 2 ^ a, one alphabet, one depth a. `bcsG`'s conclusion speaks of
random typed oracles and traces, `vlcg_eq` of one family g; Johnson/EntryRec/Core.lean
[not in this library]'s `entry_core_bcs` says what a yes on a trace gives.

-/
import Johnson.EntryRec.Defs
import Johnson.EntryRec.RecLaws

set_option autoImplicit false

namespace OnBytes.RunA

open _root_.Run _root_.Run.PQ _root_.Run.Thin _root_.Run.Twin Iop Rom Compile Compile.Batch
open Compile.Batch.Cms OnBytes.Slice

section
variable {I X RI Seed Ans : Type} [Fintype RI] [Nonempty RI] [Fintype Seed] [Nonempty Seed] {a : ℕ}
  {C : CK} {ds : List RD} {xs : List XO}
  {acc : (Seed × Ans) × (Seed × Ans) → (twoExternalStrings (2 ^ a) SgX).Str → Iop.Tr (Twin.up (SOf C ds)) → Bool}
  (T : RestR I X RI Seed Ans a (protoR (Seed × Ans) C ds a xs acc))
  (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k)
  (dec : (Seed × Ans) × (Seed × Ans) → View → Bool)

/-- The map on plain parts is the carrying along the equation between the two markings. -/
theorem embPG_eq (z : PlainPart (Twin.up (SOf C ds)) (Twin.allLo (SOf C ds))) :
    embPG T z = pbTo (Twin.allLo_eq (SOf C ds)) z := by
  cases z with
  | inl x => exact (pbTo_inl _ (Twin.allLo_eq (SL C ds)) _ x).symm
  | inr q =>
    exact (congrArg Sum.inr (embPL_eq C ds q)).trans
      (pbTo_inr _ (Twin.allLo_eq (SL C ds)) _ q).symm

/-- Link's wiring: the five fields of the skeleton's, carried to the marking "all rounds local". -/
noncomputable def wLG : ProtocolQueryLayout 256 (K + 1) (BatchInteractiveOracleProof.ofProto (LrG T).link) :=
  ⟨(wireTo (psofR_up _ C ds a xs dec) (wqR _ C K chal ds a xs dec)).sh,
    (wireTo (psofR_up _ C ds a xs dec) (wqR _ C K chal ds a xs dec)).ext,
    (wireTo (psofR_up _ C ds a xs dec) (wqR _ C K chal ds a xs dec)).decO,
    (wireTo (psofR_up _ C ds a xs dec) (wqR _ C K chal ds a xs dec)).nOpen,
    (wireTo (psofR_up _ C ds a xs dec) (wqR _ C K chal ds a xs dec)).maxDepth⟩

/-- **The whole wiring.** -/
noncomputable def WrG (wT : ProtocolQueryLayout 256 (K + 1) (BatchInteractiveOracleProof.ofProto T.test))
    (wB : ProtocolQueryLayout 256 (K + 1) T.bat) (depthReq : ℕ) : QueryLayout 256 (LrG T).carrierC :=
  wireOf (L := LrG T) (K + 1) wT (wLG T K chal dec) wB a depthReq

/-- **What runs is the run of the compiled Link verifier with the two records**, at every object of
this form, every family of typed oracle functions, every wiring of Test and of the session. -/
theorem vlcg_eq (hacc : acc = (PSofR (Seed × Ans) C ds a xs dec).accept)
    (wT : ProtocolQueryLayout 256 (K + 1) (BatchInteractiveOracleProof.ofProto T.test)) (wB : ProtocolQueryLayout 256 (K + 1) T.bat)
    (depthReq : ℕ) (g : Fam (spec 256 (K + 1) (LrG T).carrierC))
    (p : Params) (cfg : ByteArray) (cm cm' : Dig 256) (rec rec' : Seed × Ans)
    (π : OneProtocolProof 256 (PSofR (Seed × Ans) C ds a xs dec).up)
    (otabs : List (Nat × List (Nat × Row3)))
    (tabs : List (Bool × OpenB × List (List (Dig 256)))) :
    VLCG T K chal dec g p.sMT p.sFS depthReq cfg cm cm' rec rec' π otabs tabs =
      (vLC (WrG T K chal dec wT wB depthReq) p cm cm' rec rec'
        (asLinkG T dec { π with
          opens := opensOfX 0 C ds a xs (fun _ => true) otabs
          ext := extOf a cfg tabs })).det g := by
  subst hacc
  unfold VLCG
  have hw : ((wire0Less C K chal, wiresLessSL C K chal ds) : WireSLess 256 (K + 1) (SOf C ds)) =
      lessS (SOf C ds) (Twin.allLo (SOf C ds)) (wire0S C K chal, wiresSL C K chal ds)
        (((fun _ => [], fun _ => []), leavesSL C ds) : LeavesS (SOf C ds)) := by
    show _ = (lessR (wire0S C K chal) ((fun _ => [], fun _ => [])),
      lessS (SL C ds) (Twin.allLo (SL C ds)) (wiresSL C K chal ds) (leavesSL C ds))
    rw [lessS_SL]
    rfl
  rw [hw]
  refine (verifyPLO_eq (fun _ => (LrG T).carrierC) g
    (readsInOrder2 (2 ^ a)) (fun z => (z.1.map T.early, z.2)) T.late p.sMT p.sFS .link
    (PSofR (Seed × Ans) C ds a xs dec) (wire0S C K chal, wiresSL C K chal ds)
    (((fun _ => [], fun _ => []), leavesSL C ds) : LeavesS (SOf C ds))
    (decOS C ds) (weLessX a) (nOpen ds + (xs.map (·.count)).sum) (max (maxDepth ds) a)
    (fun p s => some (.inr ⟨Tag.link, ⟨p, s⟩⟩)) (embPG T)
    (fun rr => some (none, rr.1, rr.2)) (fun s => some (.inl s)) depthReq [cm, cm'] (rec, rec')
    { π with
      opens := opensOfX 0 C ds a xs (fun _ => true) otabs
      ext := extOf a cfg tabs }
    (listedX a tabs) (ownListedX ds otabs)
    ⟨fun _ _ _ => ⟨rfl, rfl⟩, leaves_SL C K chal ds⟩
    ⟨fun _ p _ _ => p.elim, fun _ p _ _ => p.elim, listed_SL C K chal otabs ds⟩).trans ?_
  refine (verifyPL_pieces (fun _ => (LrG T).carrierC) g
    (readsInOrder2 (2 ^ a)) (fun z => (z.1.map T.early, z.2)) T.late p.sMT p.sFS .link
    (PSofR (Seed × Ans) C ds a xs dec) (wqR _ C K chal ds a xs dec)
    (wire0S C K chal, wiresSL C K chal ds) (decOS C ds) (weLessX a)
    (nOpen ds + (xs.map (·.count)).sum) (max (maxDepth ds) a)
    (fun p s => some (.inr ⟨Tag.link, ⟨p, s⟩⟩)) (embPG T)
    (fun rr => some (none, rr.1, rr.2)) (fun s => some (.inl s)) depthReq [cm, cm'] (rec, rec')
    { π with
      opens := opensOfX 0 C ds a xs (fun _ => true) otabs
      ext := extOf a cfg tabs }
    (listedX a tabs) rfl rfl rfl rfl rfl
    (order2 (2 ^ a) SgX (0, [])) (extOf_listed a cfg tabs)
    (all2_complete (2 ^ a) SgX (0, []))).trans ?_
  refine (thin_reads I _ 256 (K + 1) (LrG T).carrierC g _ _
    p.sMT p.sFS .link (PSofR (Seed × Ans) C ds a xs dec) (wqR _ C K chal ds a xs dec)
    (fun p s => some (.inr ⟨Tag.link, ⟨p, s⟩⟩)) (embPG T)
    (fun rr => some (none, rr.1, rr.2)) (fun s => some (.inl s)) depthReq [cm, cm'] (rec, rec')
    { π with
      opens := opensOfX 0 C ds a xs (fun _ => true) otabs
      ext := extOf a cfg tabs }).trans ?_
  exact congrArg (fun c => OComp.det g c)
    (verifyBS_ann (lam := 256) (K := K + 1) (L := (LrG T).carrierC)
      p.sMT p.sFS .link (PSofR (Seed × Ans) C ds a xs dec).up.loc
      (Twin.allLo (SOf C ds)) (RoundSplits.allLocal (Twin.up (SOf C ds))) (Twin.allLo_eq (SOf C ds))
      (wqR _ C K chal ds a xs dec) (fun p s => some (.inr ⟨Tag.link, ⟨p, s⟩⟩))
      (embPG T) id (embPG_eq T)
      (fun rr => some (none, rr.1, rr.2)) (fun s => some (.inl s)) depthReq [cm, cm'] (rec, rec')
      { π with
        opens := opensOfX 0 C ds a xs (fun _ => true) otabs
        ext := extOf a cfg tabs })

/-- The laws of Link's wiring. -/
theorem wLG_okg (dec₀ : View → Bool) (hown : ∀ d ∈ ds, ∀ n ∈ d.opens, n < 2 ^ 16)
    (h0 : (wqS C K chal ds dec₀).OKG) : (wLG T K chal dec).OKG :=
  have h := wireTo_okg (psofR_up _ C ds a xs dec) _ (wqR_okg C K chal ds a xs _ dec dec₀ hown h0)
  ⟨h.sh, h.ext, h.opens, h.depth⟩

/-- **The laws of the wires** (`OKC`). Link's part is paid; of the two other wirings their laws are
asked. -/
theorem okc_WrG (wT : ProtocolQueryLayout 256 (K + 1) (BatchInteractiveOracleProof.ofProto T.test))
    (wB : ProtocolQueryLayout 256 (K + 1) T.bat) (depthReq : ℕ) (S : OutOfDomainSampleQueryLayout 256 (K + 1) (LrG T))
    (dec₀ : View → Bool) (hown : ∀ d ∈ ds, ∀ n ∈ d.opens, n < 2 ^ 16)
    (h0 : (wqS C K chal ds dec₀).OKG) (hS : S.OK) (okT : wT.OKG) (okB : wB.OKG)
    (slots : T.N = 2 ^ depthReq) (depT : wT.ext.depth = a) (depB : wB.ext.depth = a)
    (maxT : a ≤ wT.maxDepth) (maxB : a ≤ wB.maxDepth)
    (extT : ∀ p, wT.ext.which p = 0 ∧ wT.ext.leaf p = p.val)
    (extB : ∀ p, wB.ext.which p = 0 ∧ wB.ext.leaf p = p.val) :
    OKC (WrG T K chal dec wT wB depthReq) S :=
  okc_wireOf (L := LrG T) S okT (wLG_okg T K chal dec dec₀ hown h0) okB (le_refl _) slots
    ⟨depT, by
      show (wireTo (psofR_up _ C ds a xs dec) (wqR _ C K chal ds a xs dec)).ext.depth = a
      rw [wireTo_ext]; rfl, depB⟩
    maxT (by
      show a ≤ (wireTo (psofR_up _ C ds a xs dec) (wqR _ C K chal ds a xs dec)).maxDepth
      rw [wireTo_maxDepth]; exact le_max_right _ _) maxB extT extB
    ⟨fun p => by
        show (wireTo (psofR_up _ C ds a xs dec)
            (wqR _ C K chal ds a xs dec)).ext.which (.inl p) = 0 ∧
          (wireTo (psofR_up _ C ds a xs dec) (wqR _ C K chal ds a xs dec)).ext.leaf (.inl p) = p.val
        rw [wireTo_ext]; exact ⟨rfl, rfl⟩,
      fun p => by
        show (wireTo (psofR_up _ C ds a xs dec)
            (wqR _ C K chal ds a xs dec)).ext.which (.inr p) = 1 ∧
          (wireTo (psofR_up _ C ds a xs dec) (wqR _ C K chal ds a xs dec)).ext.leaf (.inr p) = p.val
        rw [wireTo_ext]; exact ⟨rfl, rfl⟩⟩
    hS

/-- **What the library proves of the compiled verifier with the record, at every object of this
form: every hole a named hypothesis.** -/
theorem bcsG {Wn : Type} (hacc : acc = (PSofR (Seed × Ans) C ds a xs dec).accept)
    (W : QueryLayout 256 (LrG T).carrierC) (S : OutOfDomainSampleQueryLayout 256 W.K (LrG T)) (Rno : I → X → Wn → Prop)
    (wit : X × (Seed × Ans) → (oneExternalString (2 ^ a) SgX).Str → Iop.Tr T.bat.loc.shape → Wn) (eR : ℕ)
    (εT : Err T.test.shape) (εL : Err (Twin.up (SOf C ds))) (εB : Err T.bat.loc.shape)
    (εs : ENNReal)
    (noneColl : ∀ y (rec : Seed × Ans), T.coll y rec.1 → T.dcd y rec = none)
    (rcd : ∀ y, Prob.cnt (fun s => T.coll y s) ≤ eR)
    (sndT : T.test.Sound (fun rec y => T.coll y rec.1 ∨ T.dcd y rec ≠ none) εT)
    (sndL : ∀ rr : (Seed × Ans) × (Seed × Ans), (skeletonOverBothExternalStrings C ds a xs (dec rr)).up.loc.Sound
      (fun _ y => T.dcd y.1 rr.1 = none ∨ T.coll y.2 rr.2.1 ∨ T.dcd y.2 rr.2 = T.dcd y.1 rr.1) εL)
    (sndB : ∀ rec, ((LrG T).batAt rec).SndBKT T.N T.early T.late ((LrG T).relB Rno rec)
      (fun x y τ => wit (x, rec) y τ) εB)
    (law : S.Law εs) (belowT : Err.Below εT εs) (belowL : Err.Below εL εs)
    (belowB : Err.Below εB εs) (late : T.late = none) (localT : T.test.IsLocal)
    (localB : T.bat.loc.IsLocal) (coherent : T.bat.ann.Coherent) (wires : OKC W S) :
    BcsAtC W S (fun i x => ∃ w, Rno i x w) εs := by
  subst hacc
  exact cms_bcs I X Wn 256 (LrG T) W S Rno wit eR εT εL εB εs
    ⟨noneColl, rcd, sndT, (psofR_sound C ds a xs _ dec _ εL).2 sndL, sndB⟩
    law belowT belowL belowB late localT (psofR_local C ds a xs _ dec) localB coherent wires

end

end OnBytes.RunA
