-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Joined/ExtractReads.lean: the external strings that a trace determines under the outer
roots of a file, and the two laws that the soundness proof asks of that reading.

OnBytes/TypedOracleCompiler/ holds the verifier side of the compiler beneath `innerCompiledVerifier`. It is
made for a key file's and a proof file's three hash chains, joined by seals; that it writes what is
hashed as the prover's files have it is not shown in this folder.

The general lemma of the road to soundness (`mem_of_accepted_ours`,
OnBytes/TypedOracleCompiler/Compile/Batch/SoundOurs.lean) takes the reading of the external strings off a trace as
a free function extY, and asks two things of it: it does not move from a query of the accepted
proof's own chain to the end of the trace, and a leaf that the trace determines under an outer root
gives the symbol that extY has there. This file gives the reading for any record of external
strings (`WireE`, Iop/Wire.lean) and proves both.

Main names:
  `extStr we prjE tr cms`: the string built from the leaves that tr determines under the roots cms.
  `extStr_agrees`: a determined leaf gives the symbol of `extStr`.
  `extStr_before`: outside `EM`, `extStr` is the same before a Fiat-Shamir query and at the end, if
    every root that is read occurs before that query or at it.
  `UnderTwo we cms`: every position stands under one of the first two roots of the list cms.
  `extStr_stable`: under `UnderTwo`, outside `EM`, `extStr` does not move from a query of our own
    chain (`Ours`, OnBytes/TypedOracleCompiler/Compile/Batch/Chain.lean) on.
  `extReads_extStr`: so `extStr` has `ExtReads` (OnBytes/TypedOracleCompiler/Joined/Bound.lean).
  `soundLane_extStr`: `soundLane` of that file with its hypothesis on the reading discharged.
  `rleaf_view`: the view of a leaf of the request tree is the slot value: the salt behind it is cut
    off.

Limits: `UnderTwo` cannot be dropped. The verifier reads `cms.getD (we.which p) default`; at a first
query only the first two outer roots occur (`rootFields`, OnBytes/TypedOracleCompiler/Compile/Batch/Events.lean). A
position under a third root, or under a root that the list does not hold, is read under a digest
that need not occur before our chain's queries: what stands under it can still change.
`soundLane_extStr` still asks the protocol's soundness round by round (hsnd), the bound on its
errors (hε), hN, the wire's laws, locality and coherence: none is shown here of any protocol. It
speaks of the lax verifier `Z.verifyLax`.
That the lists of outer roots with which a file's verifier is called have `UnderTwo` is shown of no
record that has a position; at a record with a position under a third root it holds of no list, and
`soundLane_extStr` then says nothing.
`soundLane_extStr` has no caller yet.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Joined.Bound

noncomputable section

namespace TypedOracleCompiler.Joined
open TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch Rom
open _root_.Compile (Tag posOf)
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open scoped ENNReal

variable {I X : Type} {lam : ℕ} {L : BatchProtocolWithLeafBody I X} {W : QueryLayout lam L} {E : ExtSpec}

/-- The external strings that a trace determines under the outer roots cms: at each position the
symbol that prjE reads from the body of the leaf that the trace determines there; the record's
filling where nothing is determined. -/
def extStr (we : WireE E) (prjE : Body L → Option E.Sym) (tr : Tc W) (cms : List (Dig lam)) :
    E.Str :=
  we.build fun p =>
    (extLeaf tr we.depth (cms.getD (we.which p) default) (we.leaf p)).bind fun z => prjE z.body

/-- A determined leaf under an outer root gives the symbol of the extracted string. -/
theorem extStr_agrees {we : WireE E} (hwe : we.OK) {embE : E.Sym → Body L}
    {prjE : Body L → Option E.Sym} (hprj : ∀ a, prjE (embE a) = some a) {tr : Tc W}
    {cms : List (Dig lam)} {p : E.Pos} {a : E.Sym} {sl : Bits}
    (h : extLeaf tr we.depth (cms.getD (we.which p) default) (we.leaf p) = some ⟨embE a, sl⟩) :
    E.rd (extStr we prjE tr cms) p = a :=
  hwe.build_rd _ p a (by rw [h]; exact hprj a)

/-- Outside `EM` the extracted string is the same before a Fiat-Shamir query and at the end, if
every root that is read occurs before that query or at it. -/
theorem extStr_before (we : WireE E) (prjE : Body L → Option E.Sym) {tr pre post : Tc W} {t : Tag}
    {q : FbIn lam L t} {a : FsAns lam W.K} (htr : tr = pre ++ fbE t q a :: post) (hM : ¬ EM tr)
    {cms : List (Dig lam)}
    (hc : ∀ p, (evM lam W.K L).OccursIn (pre ++ [fbE t q a]) (cms.getD (we.which p) default)) :
    extStr we prjE pre cms = extStr we prjE tr cms := by
  unfold extStr
  congr 1
  funext p
  rw [extLeaf_before htr hM (hc p)]

/-- Every position of the external strings stands under one of the first two roots of the list. -/
def UnderTwo (we : WireE E) (cms : List (Dig lam)) : Prop :=
  ∀ p, we.which p < 2 ∧ we.which p < cms.length

theorem UnderTwo.mem {we : WireE E} {cms : List (Dig lam)} (h : UnderTwo we cms) (p : E.Pos) :
    cms.getD (we.which p) default ∈ cms.take 2 := by
  obtain ⟨h2, hl⟩ := h p
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl, Option.getD_some]
  exact List.mem_take_iff_getElem.2 ⟨we.which p, by omega, rfl⟩

/-- Outside `EM` the extracted string does not move from a query of our own chain on. -/
theorem extStr_stable (we : WireE E) (prjE : Body L → Option E.Sym) (C : Ctx W)
    (hM : ¬ EM C.tr) (hu : UnderTwo we C.cms) {pre post : Tc W} {q : FbIn lam L C.t}
    {a : FsAns lam W.K} {l : List (Rec lam W.K L C.t)} {cur : Item lam L C.t}
    (htr : C.tr = pre ++ fbE C.t q a :: post) (ho : Ours C pre q l cur) :
    extStr we prjE pre C.cms = extStr we prjE C.tr C.cms :=
  extStr_before we prjE htr hM fun p => ours_cms C a ho _ (hu.mem p)

/-- The extracted string has what the soundness proof asks of a reading (`ExtReads`,
OnBytes/TypedOracleCompiler/Joined/Bound.lean): outside `EM`, for a lawful record of external strings whose
positions all stand under the first two outer roots, and a map prjE that reads back what embE
writes into a leaf. -/
theorem extReads_extStr (C : Ctx W) {we : WireE E} (hwe : we.OK) {embE : E.Sym → Body L}
    {prjE : Body L → Option E.Sym} (hprj : ∀ a, prjE (embE a) = some a) (hM : ¬ EM C.tr)
    (hu : UnderTwo we C.cms) : ExtReads C we embE (extStr we prjE) :=
  ⟨fun _ _ _ _ _ _ htr ho => extStr_stable we prjE C hM hu htr ho,
    fun _ _ _ h => extStr_agrees hwe hprj h⟩

/-- `soundLane` (OnBytes/TypedOracleCompiler/Joined/Bound.lean) at the extracted string: its hypothesis on the
reading is discharged. What is left of it: the map prjE with its law, and that the verifier is
called with lists of outer roots under whose first two all positions stand. -/
theorem soundLane_extStr {Y : Type} {early : Y → Y} (Z : Written W Y E) (R : ReadBack Z early)
    {N : ℕ} {Lg : Y → E.Str → Prop} {ε : Err Z.Q.loc.shape} {εs : ℝ≥0∞}
    (hsnd : Z.Q.SndBL N early L.late Lg ε) (hε : Err.Below ε εs) (hN : N = 2 ^ W.dReq Z.t)
    (hOK : Z.wq.OKG) (hloc : Z.Q.loc.IsLocal) (hco : Z.Q.ann.Coherent)
    {prjE : Body L → Option E.Sym} (hprj : ∀ a, prjE (Z.embE a) = some a) :
    SoundAt W Z.verifyLax (UnderTwo Z.wq.ext) Lg (extStr Z.wq.ext prjE) εs :=
  soundLane Z R hsnd hε hN hOK hloc hco _ _ fun _ _ _ _ hC hM =>
    extReads_extStr _ hOK.ext hprj hM hC

/-- The view of a leaf of the request tree is the slot value: the salt of the slot, which stands
behind it in the input of the leaf's query (`reqCheck`), is cut off. So extraction under a request
root finds the slot value whatever that salt is. -/
theorem rleaf_view {K : ℕ} (c : Dig lam) (rs : Bits) (r : Dig lam) :
    (pairR lam K L).leaf (⟨OracleName.rleaf, List.ofFn c ++ rs, r⟩ : QA (typedOracleFamily lam K L)) =
      some (List.ofFn c, r) := by
  show some ((List.ofFn c ++ rs).take lam, r) = _
  rw [List.take_left' (List.length_ofFn)]

end TypedOracleCompiler.Joined
