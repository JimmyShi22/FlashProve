-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Print/FormBack.lean: the goals' decoder (`decodeD`, Johnson/Goal/Tie/DescriptionOnBytes.lean)
takes the form that is printed of a whole typed proof (`formOf`, Johnson/Prover/Print/Form.lean),
and the typed proof that is laid of what it gives (`DescriptionDataAtFiles.proofOf`, Johnson/Goal/Tie/DescriptionOnDecodedProof.lean) is
that proof again.

Main names (namespace `Johnson.Prover.Print`).
  `keyRecOf_wr`, `entryAllD_wr`, `decodeD_wr`   the three makers in front of the term, at bytes that
      were written of any parsed files which their readers take: they do not refuse, all judged rows
      say yes, and what they give is said field by field. No typed proof is named
  `Fits S c q`     what is asked of the nine parts of a whole typed proof, at the configuration's
      digest c as bytes
  `PublicS S`      public, on the letters S
  `decodeD_formOf` PublicS S → Fits S c q → ∃ f, decodeD c (formOf S q) = some f ∧ S.proofOf c f
      is q

Limits. An equation of the decoder: no goal is stated, no verifier is run, no oracle is asked. That
an honest prover's parts meet `Fits`, and the letters of the goals' description `PublicS`, is not
shown here. Four clauses of `Fits` ask that typed salts of stored leaves begin with c.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Print.Form
import Johnson.Prover.Print.EntryRows
import Johnson.Prover.Print.EntryAtFull
import Johnson.Prover.Print.WholeRows
import Johnson.Prover.Print.Records
import OnBytes.Prover.Print.Whole

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Prover.Print

open VerifierAndGoals FlashProve
open VerifiableInference VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.SlotsBehindCutD
open OnBytes.Flat OnBytes.Slice OnBytes.Maker
open _root_.Run
open _root_.Iop (Dig)
open TypedOracleCompiler.Compile.Batch (OneProtocolProof)
open TypedOracleCompiler.Joined (pls₁ pls₂ pls₃)
open LPFD.Full (sBG sTG)
open PV.EntryFive (dsF xsF)
open PV.EntryInOf (LeafP Laid laidOf chainOut tabOwn tabStored KeyRec keyRecOf keyRecD entryAllD
  tieRows)
open OnBytes.Prover.Print (carrierOf Printable Canon RootsFit SizesFit wrFile wrSeeds okSeed
  read_wrFile readSeeds_wrSeeds size_magicKey)

/-! ## The makers in front of the term, at written bytes -/

/-- a list of seeds as the makers take it: elements for triples of words -/
abbrev elemsOf (sd : List (List _root_.Fmt.Ext × _root_.Fmt.Ext)) :
    List (List OnBytes.E × OnBytes.E) :=
  sd.map fun y => (y.1.map OnBytes.E.ofTriple, OnBytes.E.ofTriple y.2)

/-- **The key's root and record**, of a written parsed key file and its seeds. -/
theorem keyRecOf_wr (v lg s : ℕ) (k : Carrier.File)
    (sd : List (List _root_.Fmt.Ext × _root_.Fmt.Ext)) (hk : k.WF Carrier.magicKey)
    (h1 : sd.length < 2 ^ 64) (h2 : ∀ y ∈ sd, okSeed y) (ha : k.answers.length = 2 ^ v * s)
    (hs : sd.length = s) (hlg : ∀ y ∈ sd, y.1.length = lg) :
    ∃ r : KeyRec v lg s, keyRecOf v lg s (wrFile Carrier.magicKey k) (wrSeeds sd) = .ok r ∧
      r.cm = bytesToDig k.root ∧
      r.rcd = OnBytes.K.recOne v lg s ⟨k.root, k.answers.map OnBytes.E.ofTriple⟩ (elemsOf sd) ∧
      r.root = k.root ∧ r.answers = k.answers ∧ (r.front.drop 1).all (·.2) = true := by
  have key : ∀ x, x = keyRecOf v lg s (wrFile Carrier.magicKey k) (wrSeeds sd) →
      ∃ r : KeyRec v lg s, x = .ok r ∧ r.cm = bytesToDig k.root ∧
        r.rcd = OnBytes.K.recOne v lg s ⟨k.root, k.answers.map OnBytes.E.ofTriple⟩ (elemsOf sd) ∧
        r.root = k.root ∧ r.answers = k.answers ∧ (r.front.drop 1).all (·.2) = true := by
    intro x e
    unfold keyRecOf at e
    rw [read_wrFile Carrier.magicKey k size_magicKey.1 hk, readSeeds_wrSeeds sd h1 h2] at e
    refine ⟨_, e, rfl, rfl, rfl, rfl, ?_⟩
    simp only [List.drop_succ_cons, List.drop_zero, List.all_cons, List.all_nil, Bool.and_true,
      Bool.and_eq_true, beq_iff_eq, List.all_eq_true]
    exact ⟨ha, hs, hlg⟩
  exact key _ rfl

/-- **All in one, the full size**, of written parsed files. -/
theorem entryAllD_wr (c : ByteArray) (k : Carrier.File)
    (sd : List (List _root_.Fmt.Ext × _root_.Fmt.Ext)) (L : LeafP)
    (sd' : List (List _root_.Fmt.Ext × _root_.Fmt.Ext)) (hk : k.WF Carrier.magicKey)
    (h1 : sd.length = 1) (h2 : ∀ y ∈ sd, y.1.length = 29 ∧ okSeed y)
    (ha : k.answers.length = 2 ^ frS.P.v * 1) (hL : L.WF) (h1' : sd'.length = 1)
    (h2' : ∀ y ∈ sd', y.1.length = 29 ∧ okSeed y) (hc : c.size = 32)
    (hb : L.answers.length = 2 ^ frS.P.v * 1) (hr : L.rounds.length = dsFull.length)
    (e0 : L.root0 = k.root) (e1 : L.answers0 = k.answers) :
    ∃ rows : List (String × Bool),
      entryAllD c (wrFile Carrier.magicKey k) (wrSeeds sd) (wrLeaf L) (wrSeeds sd') =
        .ok (bytesToDig k.root,
          OnBytes.K.recOne frS.P.v 29 1 ⟨k.root, k.answers.map OnBytes.E.ofTriple⟩ (elemsOf sd),
          ⟨bytesToDig L.root,
            OnBytes.K.recOne frS.P.v 29 1 ⟨L.root, L.answers.map OnBytes.E.ofTriple⟩ (elemsOf sd'),
            c, chainOut L, tabOwn L, tabStored L⟩, rows) ∧ rows.all (·.2) = true := by
  obtain ⟨r, hr0, r1, r2, r3, r4, r5⟩ := keyRecOf_wr frS.P.v 29 1 k sd hk (by omega)
    (fun y hy => (h2 y hy).2) ha h1 fun y hy => (h2 y hy).1
  obtain ⟨m, hm0, m1, m2, m3, m4, m5, m6, m7, m8⟩ := laidOf_wr frS.P.v 29 1 dsFull.length c L sd' hL
    (by omega) (fun y hy => (h2' y hy).2) hc hb (by rw [e1]; exact ha) h1'
    (fun y hy => (h2' y hy).1) hr
  refine ⟨m.front ++ tieRows m r ++ r.front.drop 1, ?_, ?_⟩
  · unfold entryAllD keyRecD
    rw [hr0, hm0]
    show Except.ok (r.cm, r.rcd, (⟨m.cm', m.rcd', m.cfg, m.o, m.tab, m.tx⟩ : EntryIn), _) = _
    rw [r1, r2, m3, m4, m5, m6, m7, m8]
  · have t : (tieRows m r).all (·.2) = true := by
      have q1 : (r.root.size == 32) = true := by
        rw [r3, hk.root]
        rfl
      have q2 : (m.L.root0 == r.root) = true := by
        rw [m2, r3, e0]
        exact Fmt.bytes_beq_self _
      have q3 : (m.L.answers0 == r.answers) = true := by
        rw [m2, r4, e1]
        exact beq_self_eq_true _
      simp only [tieRows, List.all_cons, List.all_nil, q1, q2, q3, Bool.and_self]
    rw [List.all_append, List.all_append, t, r5]
    have m1' : m.front.all (·.2) = true := m1
    rw [m1']
    rfl

/-- **What a run does in front of the term**, of written parsed files. -/
theorem decodeD_wr (c : ByteArray) (aux : List Token) (kT : Carrier.File)
    (sd : List (List _root_.Fmt.Ext × _root_.Fmt.Ext)) (L : LeafP)
    (sd' : List (List _root_.Fmt.Ext × _root_.Fmt.Ext)) (kB : Carrier.File)
    (hk : kT.WF Carrier.magicKey) (h1 : sd.length = 1) (h2 : ∀ y ∈ sd, y.1.length = 29 ∧ okSeed y)
    (ha : kT.answers.length = 2 ^ frS.P.v * 1) (hL : L.WF) (h1' : sd'.length = 1)
    (h2' : ∀ y ∈ sd', y.1.length = 29 ∧ okSeed y) (hc : c.size = 32)
    (hb : L.answers.length = 2 ^ frS.P.v * 1) (hr : L.rounds.length = dsFull.length)
    (e0 : L.root0 = kT.root) (e1 : L.answers0 = kT.answers) (hkB : kB.WF Carrier.magicProof)
    (okT : (LKF.FileInOf.ofCarrier "key file" c kT).ok = true)
    (okB : (LKF.FileInOf.ofCarrier "proof file" c kB).ok = true) :
    decodeD c ⟨aux, wrFile Carrier.magicKey kT, wrSeeds sd, wrLeaf L, wrSeeds sd',
        wrFile Carrier.magicProof kB⟩ =
      some ⟨aux, bytesToDig kT.root,
        OnBytes.K.recOne frS.P.v 29 1 ⟨kT.root, kT.answers.map OnBytes.E.ofTriple⟩ (elemsOf sd),
        kB.copy, (LKF.FileInOf.ofCarrier "key file" c kT).inD,
        ⟨bytesToDig L.root,
          OnBytes.K.recOne frS.P.v 29 1 ⟨L.root, L.answers.map OnBytes.E.ofTriple⟩ (elemsOf sd'),
          c, chainOut L, tabOwn L, tabStored L⟩,
        (LKF.FileInOf.ofCarrier "proof file" c kB).inD⟩ := by
  obtain ⟨rows, he, hrows⟩ := entryAllD_wr c kT sd L sd' hk h1 h2 ha hL h1' h2' hc hb hr e0 e1
  have gT : LKF.FileInOf.madeKeyOf c (wrFile Carrier.magicKey kT) =
      .ok (LKF.FileInOf.ofCarrier "key file" c kT) := by
    unfold LKF.FileInOf.madeKeyOf LKF.FileInOf.madeFileOf
    rw [read_wrFile Carrier.magicKey kT size_magicKey.1 hk]
  have gB : LKF.FileInOf.madeProofOf c (wrFile Carrier.magicProof kB) =
      .ok (LKF.FileInOf.ofCarrier "proof file" c kB) := by
    unfold LKF.FileInOf.madeProofOf LKF.FileInOf.madeFileOf
    rw [read_wrFile Carrier.magicProof kB size_magicKey.2 hkB]
  unfold decodeD
  simp only [he, gT, gB, hrows, okT, okB, Bool.and_self, if_true]
  rfl

/-! ## The form of a whole typed proof -/

section
variable (C : PQ.CK) (ds : List TypedOracleCompiler.Run.PQ.RD) (a : ℕ) (xs : List PQ.XO) {X : Type}
  (dec : X → PQ.View → Bool) (root0 : ByteArray) (answers0 : List (UInt64 × UInt64 × UInt64))
  (root : ByteArray) (answers : List (UInt64 × UInt64 × UInt64))
  (π : OneProtocolProof 256 (linkSkeletonOfRoundData C ds a xs dec).up)

theorem root0_entryOf : (entryOf C ds a xs dec root0 answers0 root answers π).root0 = root0 := rfl
theorem answers0_entryOf :
    (entryOf C ds a xs dec root0 answers0 root answers π).answers0 = answers0 := rfl
theorem root_entryOf : (entryOf C ds a xs dec root0 answers0 root answers π).root = root := rfl
theorem answers_entryOf :
    (entryOf C ds a xs dec root0 answers0 root answers π).answers = answers := rfl

end

section
variable (C : PQ.CK) (D : WholeD) (tF : FrontMsg (List OnBytes.E))
  (tJ : Compile.Joined.JoinMsg (List OnBytes.E) ByteArray) (t3 : ByteArray) {Xi : Type}
  (silent : Xi → FrontMsg (List OnBytes.E) → Compile.Joined.JoinMsg (List OnBytes.E) ByteArray →
    ByteArray → Bool) (run : Xi → PQ.View → PQ.View → PQ.View → Bool) (root : ByteArray)
  (π : OneProtocolProof 256 (wholeDesc C D tF tJ t3 silent run).batch)

theorem root_carrierOf : (carrierOf C D tF tJ t3 silent run root π).root = root := rfl
theorem copy_carrierOf : (carrierOf C D tF tJ t3 silent run root π).copy =
    (pls₁ (wholeDesc C D tF tJ t3 silent run) π).1.copy := rfl
theorem answers_carrierOf : (carrierOf C D tF tJ t3 silent run root π).answers =
    (pls₁ (wholeDesc C D tF tJ t3 silent run) π).1.answers.map OnBytes.E.triple := rfl

end

/-- The fast form's record of a maker's value, field by field. -/
theorem inD_eq (m : LKF.FileInOf.MadeFile) (k : Carrier.File) (c : ByteArray)
    (pF : FrontMsg (List OnBytes.E)) (pJ : Compile.Joined.JoinMsg (List OnBytes.E) ByteArray)
    (p3 : ByteArray) (h0 : m.k = k) (h1 : m.cfg = c) (h2 : m.pF = pF) (h3 : m.pJ = pJ)
    (h4 : m.p3 = p3) : m.inD = ⟨k, c, pF, pJ, p3⟩ := by
  subst h0 h1 h2 h3 h4
  rfl

/-- The proof that is laid, where the three typings lay the three strings. For all data. -/
theorem proofE_eq {X : Type} (DK DP : WholeD)
    (runK : RecFull → PQ.View → PQ.View → PQ.View → Bool)
    (runP : X × RecFull → PQ.View → PQ.View → PQ.View → Bool) (rK rP : RecFull)
    (sT sB : OnBytes.Params.LinBindingShape) (early : X → X)
    (ds : List TypedOracleCompiler.Run.PQ.RD) (xs : List PQ.XO) (dec : RecFull × RecFull → PQ.View → Bool)
    (aux : List Token) (cm : Dig 256) (rcd : RecFull) (copy : ℕ) (c : ByteArray)
    (kT : Carrier.File) (pF : FrontMsg (List OnBytes.E))
    (pJ : Compile.Joined.JoinMsg (List OnBytes.E) ByteArray) (p3 : ByteArray) (cm' : Dig 256)
    (rcd' : RecFull) (o : _root_.Fmt.ChainOut) (tab tx : Johnson.RunOne.StrictB.Tab)
    (kB : Carrier.File) (pF' : FrontMsg (List OnBytes.E))
    (pJ' : Compile.Joined.JoinMsg (List OnBytes.E) ByteArray) (p3' : ByteArray)
    (πT : OneProtocolProof 256 (wholeDesc (ckP .two) (DK.at frS.P.T.a) (front₀ rK) (join₀ rK) ByteArray.empty
                  silK runK).batch)
    (πL : OneProtocolProof 256 (linkSkeletonOfRoundData (ckP .two) ds frS.P.T.a xs dec).up)
    (πB : OneProtocolProof 256 (wholeDesc (ckP .two) (DP.at frS.P.T.a) (front₀ rP) (join₀ rP) ByteArray.empty
                  silP runP).batch)
    (hT : kT.toBPrfAt (ckP .two) (DK.at frS.P.T.a) (front₀ rK) (join₀ rK) ByteArray.empty silK runK
      c sT pF pJ p3 = some πT)
    (hL : Johnson.RunOne.StrictW.assembleW (ckP .two) ds frS.P.T.a xs dec c o tab tx = some πL)
    (hB : kB.toBPrfAt (ckP .two) (DP.at frS.P.T.a) (front₀ rP) (join₀ rP) ByteArray.empty silP runP
      c sB pF' pJ' p3' = some πB) :
    proofE DK DP runK runP rK rP sT sB early ds xs dec aux cm rcd copy ⟨kT, c, pF, pJ, p3⟩
        ⟨cm', rcd', c, o, tab, tx⟩ ⟨kB, c, pF', pJ', p3'⟩ =
      (aux, ⟨cm, rcd⟩, ⟨copy, some πT, (cm', rcd', some πL), some πB⟩) := by
  unfold proofE piTE piLE piBE
  simp only [hT, hL, hB]
  rfl

/- The written answers stay folded: a statement at the full size's numbers is not to be unfolded. -/
attribute [local irreducible] trAns

/-- **The decoder takes the printed form, and the typed proof that is laid of it is the one that was
printed**: for all data of the three files. (The rounds' data of the entry's file are a variable
here, so that nothing is unfolded at a written list.) -/
theorem decodeD_back {X : Type} (DK DP : WholeD)
    (runK : RecFull → PQ.View → PQ.View → PQ.View → Bool)
    (runP : X × RecFull → PQ.View → PQ.View → PQ.View → Bool) (rK rP : RecFull)
    (sT sB : OnBytes.Params.LinBindingShape) (early : X → X)
    (ds : List TypedOracleCompiler.Run.PQ.RD) (xs : List PQ.XO) (dec : RecFull × RecFull → PQ.View → Bool)
    (c : ByteArray) (aux : List Token) (cm : Dig 256) (rcd : RecFull) (copy : ℕ)
    (πT : OneProtocolProof 256 (wholeDesc (ckP .two) (DK.at frS.P.T.a) (front₀ rK)
                  (join₀ rK) ByteArray.empty silK runK).batch)
    (cm' : Dig 256) (rcd' : RecFull) (πL : OneProtocolProof 256 (linkSkeletonOfRoundData (ckP .two) ds frS.P.T.a xs dec).up)
    (πB : OneProtocolProof 256 (wholeDesc (ckP .two) (DP.at frS.P.T.a) (front₀ rP)
                  (join₀ rP) ByteArray.empty silP runP).batch)
    (hfit : RootsFitL ds) (hapart : TreesApart ds) (hlen : ds.length = dsFull.length)
    (rootsK : RootsFit (DK.at frS.P.T.a)) (rootsP : RootsFit (DP.at frS.P.T.a))
    (sizesK : SizesFit (DK.at frS.P.T.a) sT) (sizesP : SizesFit (DP.at frS.P.T.a) sB)
    (liveK : (DK.at frS.P.T.a).ds₂ ≠ [] ∧ (DK.at frS.P.T.a).ds₃ ≠ [])
    (liveP : (DP.at frS.P.T.a).ds₂ ≠ [] ∧ (DP.at frS.P.T.a).ds₃ ≠ []) (c32 : c.size = 32)
    (prT : Printable (ckP .two) (DK.at frS.P.T.a) (front₀ rK) (join₀ rK) ByteArray.empty silK runK c
      sT πT)
    (cnT : Canon (ckP .two) (DK.at frS.P.T.a) (front₀ rK) (join₀ rK) ByteArray.empty silK runK πT)
    (prB : Printable (ckP .two) (DP.at frS.P.T.a) (front₀ rP) (join₀ rP) ByteArray.empty silP runP c
      sB πB)
    (cnB : Canon (ckP .two) (DP.at frS.P.T.a) (front₀ rP) (join₀ rP) ByteArray.empty silP runP πB)
    (prL : PrintableL (ckP .two) ds frS.P.T.a xs dec c πL)
    (szL : SizesL (ckP .two) ds frS.P.T.a xs dec (digToBytes cm) (trAns rcd.2) (digToBytes cm')
      (trAns rcd'.2) πL)
    (runT : Fmt.runOk (bitsToBytes πT.salt) = true ∧
      Fmt.runOk (pls₂ (wholeDesc (ckP .two) (DK.at frS.P.T.a) (front₀ rK)
      (join₀ rK) ByteArray.empty silK runK) πT).1.run = true ∧
      Fmt.runOk (pls₃ (wholeDesc (ckP .two) (DK.at frS.P.T.a) (front₀ rK)
      (join₀ rK) ByteArray.empty silK runK) πT).1 = true)
    (runB : Fmt.runOk (bitsToBytes πB.salt) = true ∧
      Fmt.runOk (pls₂ (wholeDesc (ckP .two) (DP.at frS.P.T.a) (front₀ rP)
      (join₀ rP) ByteArray.empty silP runP) πB).1.run = true ∧
      Fmt.runOk (pls₃ (wholeDesc (ckP .two) (DP.at frS.P.T.a) (front₀ rP)
      (join₀ rP) ByteArray.empty silP runP) πB).1 = true)
    (ansT : (pls₁ (wholeDesc (ckP .two) (DK.at frS.P.T.a) (front₀ rK)
      (join₀ rK) ByteArray.empty silK runK) πT).1.answers = (trAns rcd.2).map OnBytes.E.ofTriple)
    (hcopyT : (pls₁ (wholeDesc (ckP .two) (DK.at frS.P.T.a) (front₀ rK)
      (join₀ rK) ByteArray.empty silK runK) πT).1.copy = 0)
    (hcopyB : (pls₁ (wholeDesc (ckP .two) (DP.at frS.P.T.a) (front₀ rP)
      (join₀ rP) ByteArray.empty silP runP) πB).1.copy = copy) :
    ∃ f : DecodedProof,
      decodeD c ⟨aux,
        wrFile Carrier.magicKey (carrierOf (ckP .two) (DK.at frS.P.T.a) (front₀ rK) (join₀ rK)
          ByteArray.empty silK runK (digToBytes cm) πT),
        wrSeeds (seedsOf rcd),
        wrLeaf (entryOf (ckP .two) ds frS.P.T.a xs dec (digToBytes cm) (trAns rcd.2)
          (digToBytes cm') (trAns rcd'.2) πL),
        wrSeeds (seedsOf rcd'),
        wrFile Carrier.magicProof (carrierOf (ckP .two) (DP.at frS.P.T.a) (front₀ rP) (join₀ rP)
          ByteArray.empty silP runP (digToBytes cm') πB)⟩ = some f ∧
      proofE DK DP runK runP rK rP sT sB early ds xs dec f.aux f.cm f.rcd f.copy
          { f.fT with cfg := c } { f.e with cfg := c } { f.fB with cfg := c } =
        (aux, ⟨cm, rcd⟩, ⟨copy, some πT, (cm', rcd', some πL), some πB⟩) := by
  -- the three parsed files
  have wT := OnBytes.Prover.Print.wf_carrierOf (ckP .two) (DK.at frS.P.T.a) (front₀ rK)
    (join₀ rK) ByteArray.empty silK runK c (digToBytes cm) sT Carrier.magicKey
    πT rootsK sizesK prT cnT (size_digToBytes _) fun _ => hcopyT
  have wB := OnBytes.Prover.Print.wf_carrierOf (ckP .two) (DP.at frS.P.T.a) (front₀ rP)
    (join₀ rP) ByteArray.empty silP runP c (digToBytes cm') sB Carrier.magicProof
    πB rootsP sizesP prB cnB (size_digToBytes _) fun h => absurd h (by decide)
  have wL := wf_entryOf (ckP .two) ds frS.P.T.a xs dec c (digToBytes cm) (trAns rcd.2)
    (digToBytes cm') (trAns rcd'.2) πL hfit prL szL
  -- the makers' rows and silent parts
  have bT := ofCarrier_carrierOf (ckP .two) (DK.at frS.P.T.a) (front₀ rK) (join₀ rK)
    ByteArray.empty silK runK "key file" c (digToBytes cm) sT πT prT
    (size_digToBytes _) runT.1 runT.2.1 runT.2.2 liveK.1 liveK.2
  have bB := ofCarrier_carrierOf (ckP .two) (DP.at frS.P.T.a) (front₀ rP) (join₀ rP)
    ByteArray.empty silP runP "proof file" c (digToBytes cm') sB πB prB
    (size_digToBytes _) runB.1 runB.2.1 runB.2.2 liveP.1 liveP.2
  -- the records
  have zT := wf_seedsOf rcd
  have zL := wf_seedsOf rcd'
  -- the key file's answers are the key's own
  have hans : (carrierOf (ckP .two) (DK.at frS.P.T.a) (front₀ rK) (join₀ rK)
      ByteArray.empty silK runK (digToBytes cm) πT).answers = trAns rcd.2 := by
    rw [answers_carrierOf, ansT]
    exact OnBytes.Prover.Print.map_triple_ofTriple _
  have hdec := decodeD_wr c aux _ (seedsOf rcd) _ (seedsOf rcd') _ wT zT.1 zT.2.1
    (by rw [hans]; exact zT.2.2) wL zL.1 zL.2.1 c32 (by rw [answers_entryOf]; exact zL.2.2)
    ((length_roundsOfS (ckP .two) ds πL.roots πL.plains.2).trans hlen)
    (by rw [root0_entryOf, root_carrierOf]) (by rw [answers0_entryOf, hans]) wB bT.1 bB.1
  have c1 : bytesToDig (digToBytes cm) = cm := TieTree.bytes_dig _
  have c2 : bytesToDig (digToBytes cm') = cm' := TieTree.bytes_dig _
  have r1 := recOne_seedsOf (digToBytes cm) rcd
  have r2 := recOne_seedsOf (digToBytes cm') rcd'
  have eT := inD_eq (LKF.FileInOf.ofCarrier "key file" c (carrierOf (ckP .two) (DK.at frS.P.T.a)
    (front₀ rK) (join₀ rK) ByteArray.empty silK runK (digToBytes cm) πT)) _ c _ _ _
    rfl rfl bT.2.1 bT.2.2.1 bT.2.2.2
  have eB := inD_eq (LKF.FileInOf.ofCarrier "proof file" c (carrierOf (ckP .two)
    (DP.at frS.P.T.a) (front₀ rP) (join₀ rP) ByteArray.empty silP runP
    (digToBytes cm') πB)) _ c _ _ _ rfl rfl bB.2.1 bB.2.2.1 bB.2.2.2
  rw [hans, root_carrierOf, root_entryOf, answers_entryOf, copy_carrierOf, c1, c2, r1, r2,
    hcopyB, eT, eB] at hdec
  refine ⟨_, hdec, ?_⟩
  -- the three strings come back
  have hT := OnBytes.Prover.Print.toBPrfAt_carrierOf (ckP .two) (DK.at frS.P.T.a)
    (front₀ rK) (join₀ rK) ByteArray.empty silK runK c (digToBytes cm) sT
    πT rootsK prT
  have hB := OnBytes.Prover.Print.toBPrfAt_carrierOf (ckP .two) (DP.at frS.P.T.a)
    (front₀ rP) (join₀ rP) ByteArray.empty silP runP c (digToBytes cm') sB
    πB rootsP prB
  have hL := assembleW_entryOf (ckP .two) ds frS.P.T.a xs dec c (digToBytes cm)
    (trAns rcd.2) (digToBytes cm') (trAns rcd'.2) πL hfit
    hapart prL
  exact proofE_eq DK DP runK runP rK rP sT sB early ds xs
    dec aux cm rcd copy c _ _ _ _ cm' rcd' _ _ _ _ _ _ _ πT πL πB hT hL hB


variable {Zk : OnBytes.K.Pub} (S : DescriptionDataAtFiles Zk)

/-- What `decodeD_formOf` asks of the nine parts, at the configuration's digest c (as bytes). -/
structure Fits (c : ByteArray) (q : Typed S) : Prop where
  c32 : c.size = 32
  -- the three strings, each by its own predicates
  prT : Printable (ckP .two) (S.DK.at frS.P.T.a) (front₀ S.G.rec₀) (join₀ S.G.rec₀) ByteArray.empty
    silK S.runK c (sTG S.G) q.piT
  cnT : Canon (ckP .two) (S.DK.at frS.P.T.a) (front₀ S.G.rec₀) (join₀ S.G.rec₀) ByteArray.empty
    silK S.runK q.piT
  prB : Printable (ckP .two) (S.DP.at frS.P.T.a) (front₀ S.G.z₀.2) (join₀ S.G.z₀.2) ByteArray.empty
    silP S.runP c (sBG S.G) q.piB
  cnB : Canon (ckP .two) (S.DP.at frS.P.T.a) (front₀ S.G.z₀.2) (join₀ S.G.z₀.2) ByteArray.empty
    silP S.runP q.piB
  prL : PrintableL (ckP .two) dsF frS.P.T.a xsF S.dec c q.piL
  szL : SizesL (ckP .two) dsF frS.P.T.a xsF S.dec (digToBytes q.cm) (trAns q.rcd.2)
    (digToBytes q.cm') (trAns q.rcd'.2) q.piL
  -- six run values, none of them 32 zero bytes
  runT : Fmt.runOk (bitsToBytes q.piT.salt) = true ∧
    Fmt.runOk (pls₂ (wholeDesc (ckP .two) (S.DK.at frS.P.T.a) (front₀ S.G.rec₀) (join₀ S.G.rec₀)
      ByteArray.empty silK S.runK) q.piT).1.run = true ∧
    Fmt.runOk (pls₃ (wholeDesc (ckP .two) (S.DK.at frS.P.T.a) (front₀ S.G.rec₀) (join₀ S.G.rec₀)
      ByteArray.empty silK S.runK) q.piT).1 = true
  runB : Fmt.runOk (bitsToBytes q.piB.salt) = true ∧
    Fmt.runOk (pls₂ (wholeDesc (ckP .two) (S.DP.at frS.P.T.a) (front₀ S.G.z₀.2) (join₀ S.G.z₀.2)
      ByteArray.empty silP S.runP) q.piB).1.run = true ∧
    Fmt.runOk (pls₃ (wholeDesc (ckP .two) (S.DP.at frS.P.T.a) (front₀ S.G.z₀.2) (join₀ S.G.z₀.2)
      ByteArray.empty silP S.runP) q.piB).1 = true
  -- the key file's front: the key's own answers, the copy's number 0
  ansT : (pls₁ (wholeDesc (ckP .two) (S.DK.at frS.P.T.a) (front₀ S.G.rec₀) (join₀ S.G.rec₀)
    ByteArray.empty silK S.runK) q.piT).1.answers = (trAns q.rcd.2).map OnBytes.E.ofTriple
  copyT : (pls₁ (wholeDesc (ckP .two) (S.DK.at frS.P.T.a) (front₀ S.G.rec₀) (join₀ S.G.rec₀)
    ByteArray.empty silK S.runK) q.piT).1.copy = 0
  -- the proof file's front bears the copy's number
  copyB : (pls₁ (wholeDesc (ckP .two) (S.DP.at frS.P.T.a) (front₀ S.G.z₀.2) (join₀ S.G.z₀.2)
    ByteArray.empty silP S.runP) q.piB).1.copy = q.copy

/-- Public, on the letters S. -/
structure PublicS : Prop where
  rootsK : RootsFit (S.DK.at frS.P.T.a)
  rootsP : RootsFit (S.DP.at frS.P.T.a)
  sizesK : SizesFit (S.DK.at frS.P.T.a) (sTG S.G)
  sizesP : SizesFit (S.DP.at frS.P.T.a) (sBG S.G)
  liveK : S.DK.ds₂ ≠ [] ∧ S.DK.ds₃ ≠ []
  liveP : S.DP.ds₂ ≠ [] ∧ S.DP.ds₃ ≠ []

/-- **The goals' decoder takes the form, and the typed proof that is laid of it is q.** -/
theorem decodeD_formOf :
  ∀ (c : ByteArray) (q : Typed S), PublicS S → Fits S c q →
    ∃ f : DecodedProof, decodeD c (formOf S q) = some f ∧
      S.proofOf c f =
        (q.aux, ⟨q.cm, q.rcd⟩, ⟨q.copy, some q.piT, (q.cm', q.rcd', some q.piL), some q.piB⟩) :=
  fun c q hS hq =>
    decodeD_back S.DK S.DP S.runK S.runP S.G.rec₀ S.G.z₀.2 (sTG S.G) (sBG S.G) S.G.early dsF xsF
      S.dec c q.aux q.cm q.rcd q.copy q.piT q.cm' q.rcd' q.piL q.piB publicL_full.rootsFit
      publicL_full.apart rfl hS.rootsK hS.rootsP hS.sizesK hS.sizesP hS.liveK hS.liveP hq.c32 hq.prT
      hq.cnT hq.prB hq.cnB hq.prL hq.szL hq.runT hq.runB hq.ansT hq.copyT hq.copyB

end Johnson.Prover.Print
