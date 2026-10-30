-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K1/Law/ArmSyms.lean: THE PUBLIC HALF OF THE CLAUSE `SymsIn` (Johnson/Desc/K1/Law/ArmAttMats.lean: every
symbol array of the plan's matrices is named in the link's list, laid in the layout, sent, and seated at a
seat of the link's first commitment), AS A TEST WITH CODE ON PUBLIC DATA ALONE, with its law.
OBJECT: the link's written list of arrays, the layout, the request's shape, the plan's parameters tl.
USER: whoever pays JAtt | JLay (ArmAttMats.lean, ArmLayMats.lean); the witness's run at the public files.
  `symsSeatedB arrayOf lay shp l tl`   for each matrix μ < tl.NM: array number tl.gtTree μ has a name in the
                   list; the layout has an array of that name; and its message is EITHER an own message of
                   link l of moment 0 OR one of the messages that link l's group keeps from earlier links
                   (`reqGroups shp`'s field born). WHY THE SECOND ARM: at the written shape every link
                   behind the first keeps one or two messages, and by the count of the written numbers
                   their copies are tenants of the link's own first tree
  `FirstSeated own a l`   THE STATE's HALF, WHAT IS LEFT: at the part a each own message of moment 0 of link l,
                   and each kept message, is there (`ReqFrame.whereIs`) and sits at a seat of own
  `symsIn_of_B`      **the law**: the test at the part's own list, layout and shape, and FirstSeated: SymsIn
  `symsIn_at_reads`  the same inside the fence, at THE WRITTEN list, layout and shape (arrays_at_reads · LiveIs)
  `symsAllB`, `symsLooked`   all 25 links at `Look.tlAt X`; how many arrays the test looks at
  four kernel evaluations at the written shape and a made-up layout of four arrays: an own array of moment 0
  and a kept array pass; BENT: an array in an earlier link's message that is NOT kept, and an own array of
  moment 1, are rejected
What is not claimed. The test's value at any public file. FirstSeated at any state. Nothing on soundness.
The recursion limit is raised in this file (maxRecDepth 1000000): for the kernel's evaluations'
elaboration alone.

-/
import Johnson.Desc.K1.Law.ArmLayMats

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.First (S Meaning)
open VerifiableInference.Desc.Sound (linksFull MsgT MgData CellsQ linkNo)
open VerifiableInference.Desc.K12.Door (K12Data)
open VerifiableInference.Desc.ReqLit (shapeFull)
open OnBytes.Model.Stages (LinkH)
open OnBytes.Params (Rounds)
open Iop Run OnBytes.Maker OnBytes.Flat
open Cb Johnson.Pack
open ProofFile (Cl)

/-- Message number k of link born is an own message of link l of moment 0, or one that link l's group
keeps. -/
def firstOrKeptB (shp : ReqShape) (l born k : ℕ) : Bool :=
  if born == l then
    match (shp.link[l]?).bind fun L => L.messages[k]? with
    | some m => m.moment == 0
    | none => false
  else ((reqGroups shp).getD l {}).born.contains (born, k)

/-- **The test on public data.** -/
def symsSeatedB (arrayOf : Array (ℕ × String)) (lay : ReqLayout) (shp : ReqShape) (l : ℕ)
    (tl : HTailF2) : Bool :=
  (List.range tl.NM).all fun μ =>
    match arrayOf[tl.gtTree.getD μ 0]? with
    | none => false
    | some b =>
      match reqArray lay b.1 b.2 with
      | none => false
      | some Ar => firstOrKeptB shp l b.1 Ar.message

/-- **The state's half.** -/
def FirstSeated (own : List (ℕ × ℕ)) (a : K9.Part) (l : ℕ) : Prop :=
  ∀ born k, firstOrKeptB a.L.check.frame.shape l born k = true →
    ∃ o x, a.L.check.frame.whereIs born k = some o ∧ K9.seatAt own a.d.book o = some x

/-- **The law.** -/
theorem symsIn_of_B {own : List (ℕ × ℕ)} {a : K9.Part} {l : ℕ} {tl : HTailF2}
    (hB : symsSeatedB a.L.arrayOf a.L.check.rows.layout a.L.check.frame.shape l tl = true)
    (hF : FirstSeated own a l) : SymsIn own a tl := by
  intro μ hμ
  have h := List.all_eq_true.1 hB μ (List.mem_range.2 hμ)
  cases e1 : a.L.arrayOf[tl.gtTree.getD μ 0]? with
  | none =>
    rw [e1] at h
    cases h
  | some b =>
    rw [e1] at h
    dsimp only at h
    cases e2 : reqArray a.L.check.rows.layout b.1 b.2 with
    | none =>
      rw [e2] at h
      cases h
    | some Ar =>
      rw [e2] at h
      obtain ⟨o, x, h3, h4⟩ := hF b.1 Ar.message h
      unfold K9.arrayIn
      rw [e1, Option.bind_some, e2, Option.bind_some, h3, Option.bind_some, h4]
      rfl

section
variable {Xi Tok : Type} {rows cols nR : ℕ} {XV : OnBytes.Model.Verify.Public}
  (Dm : MgData Xi ProofFile.InstPub Tok rows cols nR XV) (dk : K12Data)
  (Mg₀ : Meaning ProofFile.InstPub (Wit (CellsQ rows cols) Tok MsgT))

/-- **Inside the fence, at the written list, layout and shape.** -/
theorem symsIn_at_reads {J : S → Prop} (hM : Mg₀.more = {}) {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {aN : ℕ}
    {R₁ R₂ R₃ : Rounds} {c : Chain S Cl} {l : ℕ} {X : LinkH} {arrs : Option (List ℕ)}
    {x x' : ProofFile.InstPub × S} {y y' : Strs} {w : Wit (CellsQ rows cols) Tok MsgT} {p : ℕ × String}
    {A B : K9.Part} (Fc : ReadsFence Dm dk Mg₀ J Z Bs aN R₁ R₂ R₃ c l X arrs x x' y y' w p A B)
    {shp : ReqShape} {lay₀ : ReqLayout} (hJl : ∀ s, J s → LiveIs shp lay₀ s) {tl : HTailF2}
    (hB : symsSeatedB (Dm.pubD.d3.arrayOf.getD l #[]) lay₀ shp l tl = true)
    (hF : FirstSeated (Dm.N.sent l 0) A l) : SymsIn (Dm.N.sent l 0) A tl := by
  obtain ⟨_, hLa, _, _, _⟩ := segAt_some Fc.front
  have hlive : x.2.live = A.L.check := by
    unfold S.live
    rw [hLa]
  obtain ⟨eS, eL⟩ := hJl _ Fc.inv
  rw [hlive] at eS eL
  refine symsIn_of_B ?_ hF
  rw [arrays_at_reads Dm dk Mg₀ hM l Fc.lt x y Fc.inAt A Fc.front, eS, eL]
  exact hB

end

/-- All 25 links, at the public parameters' own parameters of the approximate range proof. -/
def symsAllB (X : Verify.Public) (arrayOf : Array (Array (ℕ × String))) (lay : ReqLayout)
    (shp : ReqShape) : Bool :=
  (List.range 25).all fun l =>
    symsSeatedB (arrayOf.getD l #[]) lay shp l ((First.Look.tlAt X l).getD {})

/-- How many arrays symsAllB looks at. -/
def symsLooked (X : Verify.Public) : ℕ :=
  ((List.range 25).map fun l => ((First.Look.tlAt X l).getD {}).NM).sum

/-! ## Controls: the written shape; a made-up layout -/

/-- Four made-up arrays: in messages 0 (not kept) and 1 (kept by link 1) of link 0; in messages 0
(moment 0) and 1 (moment 1) of link 1. -/
def toyLay : ReqLayout :=
  ⟨[[⟨"a", 0, 1, 1, []⟩, ⟨"b", 1, 1, 1, []⟩], [⟨"c", 0, 1, 1, []⟩, ⟨"d", 1, 1, 1, []⟩]]⟩

theorem syms_own : symsSeatedB #[(1, "c")] toyLay shapeFull 1 { NM := 1, gtTree := #[0] } = true := by
  decide +kernel

theorem syms_kept : symsSeatedB #[(0, "b")] toyLay shapeFull 1 { NM := 1, gtTree := #[0] } = true := by
  decide +kernel

/-- **BENT**: the matrix's symbols' array lies in an earlier link's message that link 1 does not keep. -/
theorem syms_fails_earlier :
    symsSeatedB #[(0, "a")] toyLay shapeFull 1 { NM := 1, gtTree := #[0] } = false := by
  decide +kernel

/-- **BENT**: it lies in the link's own message of moment 1. -/
theorem syms_fails_later :
    symsSeatedB #[(1, "d")] toyLay shapeFull 1 { NM := 1, gtTree := #[0] } = false := by
  decide +kernel

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.symsIn_of_B
#print axioms VerifiableInference.Desc.K1.symsIn_at_reads
#print axioms VerifiableInference.Desc.K1.syms_own
#print axioms VerifiableInference.Desc.K1.syms_kept
#print axioms VerifiableInference.Desc.K1.syms_fails_earlier
#print axioms VerifiableInference.Desc.K1.syms_fails_later
