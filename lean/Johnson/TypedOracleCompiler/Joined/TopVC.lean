-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/TypedOracleCompiler/Joined/TopVC.lean: index binding of the verifier with records, where the key's file and
the proof's file are three joined hash chains each, from the soundness clause of each chain.

Statements on the verifier with records, over the second form of the compiler's verifier side, for a
key file's and a proof file's three hash chains, joined by seals. That this verifier writes what is
hashed as the prover's files have it is not shown in this folder.
By a reading of the programs' text it does not: behind the roots, `VC`
(Johnson/TypedOracleCompiler/RecCompile/Cms.lean) puts a code of the whole record, the seed too, into the first
query of each of its three compiled verifiers, while the programs hash the roots and the answers,
and recompute the seeds from the roots (so too the verifier written in Lean:
OnBytes/Params/Chains.lean; OnBytes/Key/Table.lean). `verifyAtFullKey` (Johnson/TypedOracleCompiler/RecCompile/CmsAns.lean) is
the form that has the answers alone there; nothing in this file is stated for it.

Theorems of other files are put one behind the other; nothing else is proved here.
  OnBytes/TypedOracleCompiler/Joined/LandRec.lean (`soundAtR_of_files`, `soundAtR_of_files_late`): from the typed
    descriptions of the key's and of the proof's three chains, each chain with its soundness clause
    (`Links.Knows`, `Links.KnowsLate`, OnBytes/TypedOracleCompiler/Joined/Top.lean), to `L.SoundAtR`
    (Hiop/RecInterface.lean) of an interface whose `offline` and `onlineBatch` are the two joined protocols.
  Johnson/TypedOracleCompiler/RecCompile/Pass.lean (`cms_binding_at`): from `L.SoundAtR` to index binding of every
    scheme whose verifier is `VC`: the seeds' queries, then the compiled verifier of the key, of the
    link and of the session.

Main names:
  `binding_of_files`       where no later query of a session takes in more of the instance
  `binding_of_files_late`  where the query of round n of the proof's first chain does
  `vTC_walk`, `vBC_walk`   under the same premises on the interface, the calls of `VC` for the key
                           and for a session's proof ARE the verifier that walks a file's three
                           chains one after the other (Johnson/TypedOracleCompiler/Joined/VCWalk.lean; the whole
                           of `VC` written with the two walks: `VC_eq_files` there)

Every hypothesis stands in the statements under its own name. Of the descriptions: knowsT, knowsB,
decidesT, decidesB, tieT, tieB, lawsT, lawsB, hlT, hlB (late: idem, pos, inFirst). Of the record and
the link: noneColl, rcd, sndL, hlL, hcL, hSd. Of the numbers: hbT, hbL, hbB. Of the wires: hW. hT,
hB, haT, hl say which interface it is: `L.offline` and `L.onlineBatch` are the two files' protocols, and the
key's is run with the annotation of its three joined chains. Where that is so by unfolding, hT and
hB are rfl, haT is HEq.rfl and the casts are the identity.

Limits: none of these hypotheses is shown here of a real file. That those of `binding_of_files_late`
can be met together is shown at one small object (`toy_binding`, Johnson/TypedOracleCompiler/Joined/ToyVC.lean),
where hash values have one bit, so that the bound is at least 1 and the conclusion says nothing
there. εs is a letter above the errors. The theorems are said of the object as it is handed in, with
plain errors: no proof of work is counted, and the wires' laws (hW) ask an exactly uniform verifier
message in every round, which holds where a round's message is the hash's blocks: so L is meant to
be an object that has already gone through the library's two passes (samplers; proof-of-work bits),
and the two files' descriptions are then descriptions of its rounds after the passes.
`cms_binding_work` of the same file, which starts before the passes and counts work, is not composed
here. What the heads of the files named above do not claim.
The game is over the family of typed oracles, each drawn: no coding of them into one hash function
on strings stands in these statements. hbT and hbL ask εs above a shared round's error counted once
for each leaf of the request tree (2 ^ depthReqT, 2 ^ depthReqL), hbB above the second chain's
errors counted `L.maxBatchSize` times: a tree of depth d costs d bits in its shared rounds.
`binding_of_files` is applied nowhere in the library yet: that its hypotheses can be met together is
not shown.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Joined.LandRec
import Johnson.TypedOracleCompiler.RecCompile.Pass
import Johnson.TypedOracleCompiler.Joined.VCWalk

set_option autoImplicit false

noncomputable section

namespace TypedOracleCompiler.Compile.Batch.Cms
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Joined Rom Prob
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Compile.Joined (Chains Desc)
open scoped ENNReal

variable {I X Wn ISK : Type} {lam : ℕ} {Bd : Type}

/-! ## Laws of a file's protocol, at a protocol that is equal to it -/

section Eq
variable {Y : Type} {E : ExtSpec} {G : Chains}

theorem isLocal_of_eq {P₀ : InteractiveOracleProof Y E} : ∀ P : InteractiveOracleProof Y E, P = P₀ → P₀.IsLocal → P.IsLocal := by
  rintro _ rfl h
  exact h

theorem coherent_of_test (D : Desc G Y E) (h : G.Laws) :
    ∀ (P : InteractiveOracleProof Y E) (_ : P = D.proto) (a : RoundSplits P.shape), HEq a G.ann → a.Coherent := by
  rintro _ rfl a ha
  obtain rfl := eq_of_heq ha
  exact G.ann_coherent h

theorem coherent_of_bat (D : Desc G Y E) (h : G.Laws) :
    ∀ Q : BatchInteractiveOracleProof Y E, Q = D.batch → Q.ann.Coherent := by
  rintro _ rfl
  exact G.ann_coherent h

end Eq

variable (L : HolographicProtocol I X) {GT GB : Chains} (DT : Desc GT L.Rec (oneExternalString L.wordLength L.Symbol))
  (DB : Desc GB (X × L.Rec) (oneExternalString L.wordLength L.Symbol)) {CT : Links GT (L.Rec × (oneExternalString L.wordLength L.Symbol).Str)}
  {CB : Links GB ((X × L.Rec) × (oneExternalString L.wordLength L.Symbol).Str)} (Ryes Rno : I → X → Wn → Prop)
  (wit : X × L.Rec → (oneExternalString L.wordLength L.Symbol).Str → Tr GB.sh → Wn) (eR : ℕ) (εL : Err L.link.shape)
  (hT : L.offline = DT.proto) (hB : L.onlineBatch = DB.batch) (εs : ℝ≥0∞)
  (sub : ∀ i x, (∃ w, Ryes i x w) → ∃ w, Rno i x w)

section At
variable {aT : RoundSplits L.offline.shape} {aL : RoundSplits L.link.shape}
  (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL) (p : Params)

/-- **Index binding of the verifier with records, from the soundness clause of each chain of the
key's and of the proof's file**, where no later query of a session takes in more of the instance
(hl). haT: the key's protocol is run with the annotation of its three joined chains. The relation of
the proof's description speaks of `L.early x` alone: what `L.early` drops of an instance is reached
only through tieB, from the verifier's yes at x and the transcript. -/
theorem binding_of_files (hl : L.late = none)
    (noneColl : ∀ y (rec : L.Rec), L.hasCollisionAt y rec.1 → L.decodeIndex y rec = none)
    (rcd : ∀ y, Prob.cnt (fun s => L.hasCollisionAt y s) ≤ eR)
    (sndL : L.link.Sound
      (fun rr y => L.decodeIndex y.1 rr.1 = none ∨ L.hasCollisionAt y.2 rr.2.1 ∨ L.decodeIndex y.2 rr.2 = L.decodeIndex y.1 rr.1) εL)
    (knowsT : CT.Knows)
    (decidesT : ∀ x y (τ : Tr GT.sh),
      DT.accept x y τ = true → (CT.all.out (x, y) τ).isSome = true)
    (tieT : ∀ rec y, CT.Lg id rec y → L.hasCollisionAt y rec.1 ∨ L.decodeIndex y rec ≠ none)
    (lawsB : GB.Laws) (knowsB : CB.Knows)
    (decidesB : ∀ x rec y (τ : Tr GB.sh), DB.accept (x, rec) y τ = true →
      (CB.all.out ((L.early x, rec), y) τ).isSome = true)
    (tieB : ∀ x rec y (τ : Tr GB.sh), DB.accept (x, rec) y τ = true →
      (CB.on₀ ((L.early x, rec), y) →
        CB.R₀ ((L.early x, rec), y) (CB.ext ((L.early x, rec), y) τ ())) →
      L.relB Rno rec x y (wit (x, rec) y τ))
    (hSd : S.Law εs)
    (hbT : Err.Below (Err.timesShared (2 ^ W.depthReqT) aT
      (cast (congrArg (fun Q : InteractiveOracleProof _ _ => Err Q.shape) hT.symm) CT.err)) εs)
    (hbL : Err.Below (Err.timesShared (2 ^ W.depthReqL) aL εL) εs)
    (hbB : Err.Below
      (cast (congrArg (fun Q : BatchInteractiveOracleProof _ _ => Err Q.loc.shape) hB.symm) (CB.errN L.maxBatchSize)) εs)
    (haT : HEq aT GT.ann) (lawsT : GT.Laws) (hlT : DT.proto.IsLocal) (hlL : L.link.IsLocal)
    (hlB : DB.proto.IsLocal) (hcL : aL.Coherent) (hW : OKC W S)
    (A : ZKCP.Gen.Arg (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) I X Unit (FullKey lam L aT aL) ISK
      (RequestProof lam L))
    (hA : A.V = VC W S p) :
    ZKCP.Gen.HasIndexBindingWith
      (relPair (fun i x => ∃ w, Ryes i x w) (fun i x => ∃ w, Rno i x w) sub)
      A (extractorC0 W) (epsC W εs) :=
  cms_binding_at W S p Ryes Rno _ eR _ εL _ εs sub
    (soundAtR_of_files L DT DB Rno wit eR εL hT hB hl noneColl rcd sndL knowsT decidesT tieT lawsB
      knowsB decidesB tieB)
    hSd hbT hbL hbB (isLocal_of_eq L.offline hT hlT) hlL
    (isLocal_of_eq L.onlineBatch.loc (congrArg BatchInteractiveOracleProof.loc hB) hlB)
    (coherent_of_test DT lawsT L.offline hT aT haT) hcL (coherent_of_bat DB lawsB L.onlineBatch hB) hW A hA

/-- **The same**, where the query of round n of the proof's first chain takes in the rest of the
instance (hl). -/
theorem binding_of_files_late (n : ℕ) (hl : L.late = some n)
    (noneColl : ∀ y (rec : L.Rec), L.hasCollisionAt y rec.1 → L.decodeIndex y rec = none)
    (rcd : ∀ y, Prob.cnt (fun s => L.hasCollisionAt y s) ≤ eR)
    (sndL : L.link.Sound
      (fun rr y => L.decodeIndex y.1 rr.1 = none ∨ L.hasCollisionAt y.2 rr.2.1 ∨ L.decodeIndex y.2 rr.2 = L.decodeIndex y.1 rr.1) εL)
    (knowsT : CT.Knows)
    (decidesT : ∀ x y (τ : Tr GT.sh),
      DT.accept x y τ = true → (CT.all.out (x, y) τ).isSome = true)
    (tieT : ∀ rec y, CT.Lg id rec y → L.hasCollisionAt y rec.1 ∨ L.decodeIndex y rec ≠ none)
    (lawsB : GB.Laws) (knowsB : CB.KnowsLate (fun a : X × L.Rec => (L.early a.1, a.2)) n)
    (decidesB : ∀ x rec y (τ : Tr GB.sh), DB.accept (x, rec) y τ = true →
      (CB.all.out ((x, rec), y) τ).isSome = true)
    (idem : ∀ x, L.early (L.early x) = L.early x) (pos : 0 < n) (inFirst : n ≤ GB.s₁.length)
    (tieB : ∀ x rec y (τ : Tr GB.sh), DB.accept (x, rec) y τ = true →
      (CB.on₀ ((x, rec), y) → CB.R₀ ((x, rec), y) (CB.ext ((x, rec), y) τ ())) →
      L.relB Rno rec x y (wit (x, rec) y τ))
    (hSd : S.Law εs)
    (hbT : Err.Below (Err.timesShared (2 ^ W.depthReqT) aT
      (cast (congrArg (fun Q : InteractiveOracleProof _ _ => Err Q.shape) hT.symm) CT.err)) εs)
    (hbL : Err.Below (Err.timesShared (2 ^ W.depthReqL) aL εL) εs)
    (hbB : Err.Below
      (cast (congrArg (fun Q : BatchInteractiveOracleProof _ _ => Err Q.loc.shape) hB.symm) (CB.errN L.maxBatchSize)) εs)
    (haT : HEq aT GT.ann) (lawsT : GT.Laws) (hlT : DT.proto.IsLocal) (hlL : L.link.IsLocal)
    (hlB : DB.proto.IsLocal) (hcL : aL.Coherent) (hW : OKC W S)
    (A : ZKCP.Gen.Arg (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) I X Unit (FullKey lam L aT aL) ISK
      (RequestProof lam L))
    (hA : A.V = VC W S p) :
    ZKCP.Gen.HasIndexBindingWith
      (relPair (fun i x => ∃ w, Ryes i x w) (fun i x => ∃ w, Rno i x w) sub)
      A (extractorC0 W) (epsC W εs) :=
  cms_binding_at W S p Ryes Rno _ eR _ εL _ εs sub
    (soundAtR_of_files_late L DT DB Rno wit eR εL hT hB n hl noneColl rcd sndL knowsT decidesT tieT
      lawsB knowsB decidesB idem pos inFirst tieB)
    hSd hbT hbL hbB (isLocal_of_eq L.offline hT hlT) hlL
    (isLocal_of_eq L.onlineBatch.loc (congrArg BatchInteractiveOracleProof.loc hB) hlB)
    (coherent_of_test DT lawsT L.offline hT aT haT) hcL (coherent_of_bat DB lawsB L.onlineBatch hB) hW A hA

/-- **Under the same premises hT, haT: the call of `VC` for the key is the verifier of the key's
file, which walks its three chains one after the other** (`FileW.verify`,
OnBytes/TypedOracleCompiler/Joined/Verifier.lean), at the file made of W's own wire record and maps. The proof
string is carried along an equation of two protocols; where hT and haT hold by unfolding nothing is
carried. -/
theorem vTC_walk (haT : HEq aT GT.ann) (cm : Dig lam) (rec : L.Rec)
    (π : OneProtocolProof lam (batTC L aT)) :
    vTC W S p cm rec π =
      (FileW.ofWritten (writtenT W) DT (batch_eq_of_proto DT L.offline hT aT haT)).verify p.sMT p.sFS
        (cmsT W S cm rec) rec
        (cast (congrArg (fun Q : BatchInteractiveOracleProof L.Rec (oneExternalString L.wordLength L.Symbol) => OneProtocolProof lam Q)
          (batch_eq_of_proto DT L.offline hT aT haT)) π) :=
  vTC_eq_file W S DT (batch_eq_of_proto DT L.offline hT aT haT) p cm rec π

/-- **Under the same premise hB: the call of `VC` for a session's proof is the verifier of the
proof's file, which walks its three chains one after the other.** -/
theorem vBC_walk (cm : Dig lam) (x : X) (rec : L.Rec) (π : OneProtocolProof lam L.onlineBatch) :
    vBC W S p cm x rec π =
      (FileW.ofWritten (writtenB W) DB hB).verify p.sMT p.sFS (cmsB W S cm rec) (x, rec)
        (cast (congrArg (fun Q : BatchInteractiveOracleProof (X × L.Rec) (oneExternalString L.wordLength L.Symbol) => OneProtocolProof lam Q) hB) π) :=
  vBC_eq_file W S DB hB p cm x rec π

end At

end TypedOracleCompiler.Compile.Batch.Cms
