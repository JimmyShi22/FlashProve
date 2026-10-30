-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/ListedSteps.lean: the part of the verifier along lists that stands behind the chain
(OnBytes/TypedOracleCompiler/Compile/Batch/ListedVerifier.lean: strictBBL, afterBOL), said again as a list of named
tests, each behind a thunk. Definitions; they have code.

No soundness: a test. This module serves the runs of lean/Ask/; it states nothing on soundness.

What it is for. A file that runs the verifier at a real file can print each test's answer as soon as
the test is made: a "no" then has a name, and a run that ends early has told what it had found.

Main names:
  `Steps`: a list of names, each with a test behind a thunk. `Steps.yes`: every test says yes.
  `firstNo`: of a list of names with answers, the first name that says no.
  `behindSteps`: for the chain's value (ρ, rts, ph) and a family g of oracle answers: the seven
    conjuncts of strictBBL; whether forestsBL and forestExtL return; the two bounds of afterBOL; the
    forests' run; the request tree's part; accept. Fourteen lines. Where a forest is lacking, each
    of the last five says no.
  `acceptSteps`: at the description of a whole file: the nine conjuncts of reductionOfWholeFile's out
    (OnBytes/Maker/Whole.lean), in its order.
  `wholeSteps`: the two at a whole file, with the read leaves and positions of
    OnBytes/Maker/ListedWhole.lean. Twenty-three lines.
Limits: definitions alone. That every line says yes just where strictBBL and afterBOL say yes is not
shown in this file. The line "after 5" and the nine lines of acceptSteps make the same test twice.
The lines "strict 3" and "strict 4" test openings at the places in the lists own and listed alone
(where openings are in the proof string); an opening at another place is not seen by them. Nothing
on time or memory is a theorem. Nothing on soundness.
The program does not import this file.


-/
import OnBytes.Maker.ListedWhole

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Maker

/-- Names, each with a test behind a thunk. -/
abbrev Steps : Type := List (String × Thunk Bool)

/-- Every test says yes. -/
def Steps.yes (l : Steps) : Bool := l.all fun x => x.2.get

/-- The first name that says no. -/
def firstNo (l : List (String × Bool)) : Option String := (l.find? fun x => !x.2).map (·.1)

/-- Two lists, if both are there. -/
def bothF {α : Type} : Option (List α) → Option (List α) → Option (List α)
  | some a, some b => some (a ++ b)
  | _, _ => none

/-- A test on what is there; no where nothing is. -/
def onF {α : Type} (p : α → Bool) : Option α → Bool
  | some a => p a
  | none => false

section Letters
open TypedOracleCompiler.Compile.Batch
open _root_.Compile TypedOracleCompiler.Iop Rom
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable {I X : Type} {lam K : ℕ} {L : BatchProtocolWithLeafBody I X}

/-- The part behind the chain, test by test. -/
def behindSteps (sMT sFS : ℕ) {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E)
    (sh : RoundsQueryLayout lam K Q.loc.shape Q.ann) (wl : WireELess E) (nOpen maxDepth : ℕ)
    (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L) (embE : E.Sym → Body L)
    (depthReq : ℕ) (cms : List (Dig lam)) (x : Y) (π : OneProtocolProof lam Q) (own : Leaves)
    (listed : List E.Pos) (rd : Leaves) (rdE : List E.Pos) (g : Fam (typedOracleFamily lam K L))
    (ρ : Rho Q.loc.shape) (rts : RootsOfChain lam Q.loc.shape) (ph : Phase lam) : Steps :=
  haveI := wl.dec
  let fB : Thunk (Option (List (Forest lam L))) :=
    Thunk.mk fun _ => forestsBL Q.loc.shape Q.ann sh embS rts π.opens rd
  let fE : Thunk (Option (List (Forest lam L))) :=
    Thunk.mk fun _ => forestExtL wl embE cms π.ext rdE
  let Fs : Thunk (Option (List (Forest lam L))) := Thunk.mk fun _ => bothF fB.get fE.get
  [("strict 1: the salt has its length", Thunk.mk fun _ => decide (π.salt.length = sFS)),
    ("strict 2: no more roots than the chain took",
      Thunk.mk fun _ => decide (π.roots.length ≤ RootsOfChain.count Q.loc.shape rts)),
    ("strict 3: the file's own trees: openings at read leaves alone, salts of their length",
      Thunk.mk fun _ => strictSBL sMT Q.loc.shape Q.ann sh rts π.opens own rd),
    ("strict 4: the stored table: openings at read positions alone, salts of their length",
      Thunk.mk fun _ => strictExtL sMT (fun p => rdE.contains p) π.ext listed),
    ("strict 5: the slot's number is below the number of slots",
      Thunk.mk fun _ => decide (π.slot < 2 ^ depthReq)),
    ("strict 6: no path is given unless the chain gave a slot value",
      Thunk.mk fun _ => ph.slotVal.isSome || π.path.isEmpty),
    ("strict 7: no salt of the slot is given unless the chain gave a slot value",
      Thunk.mk fun _ => ph.slotVal.isSome || π.rsalt.isEmpty),
    ("forests 1: the file's own trees: every read leaf has its opening",
      Thunk.mk fun _ => fB.get.isSome),
    ("forests 2: the stored table: every read position has its opening",
      Thunk.mk fun _ => fE.get.isSome),
    ("after 1: no more openings than the description allows",
      Thunk.mk fun _ => onF (fun F => decide ((flatF F).length ≤ nOpen)) Fs.get),
    ("after 2: every opening well formed and no deeper than the description allows",
      Thunk.mk fun _ =>
        onF (fun F => (flatF F).all fun c => c.wellFormed && decide (c.depth ≤ maxDepth)) Fs.get),
    ("after 3: the openings lead to their roots",
      Thunk.mk fun _ => onF (fun F => (runForests F (readsF F)).det g) Fs.get),
    ("after 4: the slot's leaf leads to the binding root",
      Thunk.mk fun _ => onF (fun _ => (reqPart depthReq π ph).det g) Fs.get),
    ("after 5: the description's own decision, whole",
      Thunk.mk fun _ => onF (fun _ => Q.loc.accept x (wl.build fun p => (π.ext p).map Opening.sym)
        (mkTr Q.loc.shape Q.ann sh rts π.plains ρ π.opens)) Fs.get)]

end Letters

section Whole
open TypedOracleCompiler.Iop TypedOracleCompiler.Joined TypedOracleCompiler.Compile.Batch _root_.Compile.Joined
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run _root_.Run.PQ

variable (C : CK) (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k) (D : WholeD)
  {TF TJ T3 : Type} (tF : TF) (tJ : TJ) (t3 : T3)
  {Xi : Type} (silent : Xi → TF → TJ → T3 → Bool) (run : Xi → View → View → View → Bool)

/-- The nine conjuncts of reductionOfWholeFile's out, in its order. -/
def acceptSteps (x : Xi) (y : (oneExternalString (2 ^ D.a) SgX).Str)
    (τ : _root_.Iop.Tr (chainsOf C D tF tJ t3).sh) : Steps :=
  let τ₁ := (chainsOf C D tF tJ t3).tr₁ τ
  let τ₂ := (chainsOf C D tF tJ t3).tr₂ τ
  let τ₃ := (chainsOf C D tF tJ t3).tr₃ τ
  let R₁ := Thunk.mk fun _ => drawnT C D.ds₁ (rhoT C D.ds₁ τ₁)
  let R₂ := Thunk.mk fun _ => drawnT C D.ds₂ (rhoT C D.ds₂ τ₂)
  let R₃ := Thunk.mk fun _ => drawnT C D.ds₃ (rhoT C D.ds₃ τ₃)
  let w₁ := Thunk.mk fun _ => wantsOf D.a D.depth D.ds₁ R₁.get
  let w₂ := Thunk.mk fun _ => wantsOf D.a D.depth D.ds₂ R₂.get
  let w₃ := Thunk.mk fun _ => wantsOf D.a D.depth D.ds₃ R₃.get
  [("accept 1: the first chain's proofs of work pass",
      Thunk.mk fun _ => passT C D.ds₁ (rhoT C D.ds₁ τ₁)),
    ("accept 2: the second chain's proofs of work pass",
      Thunk.mk fun _ => passT C D.ds₂ (rhoT C D.ds₂ τ₂)),
    ("accept 3: the third chain's proofs of work pass",
      Thunk.mk fun _ => passT C D.ds₃ (rhoT C D.ds₃ τ₃)),
    ("accept 4: the first chain's draws are complete", Thunk.mk fun _ => fullOf D.ds₁ R₁.get),
    ("accept 5: the second chain's draws are complete", Thunk.mk fun _ => fullOf D.ds₂ R₂.get),
    ("accept 6: the third chain's draws are complete", Thunk.mk fun _ => fullOf D.ds₃ R₃.get),
    ("accept 7: the stored table's symbols carry their own positions",
      Thunk.mk fun _ => carriesOf D y (w₁.get ++ (w₂.get ++ w₃.get))),
    ("accept 8: what is sent in the three rounds without a challenge fits the claim",
      Thunk.mk fun _ => silent x ((chainsOf C D tF tJ t3).msgF τ).2
        ((chainsOf C D tF tJ t3).msgJ τ).2 ((chainsOf C D tF tJ t3).msg3 τ).2),
    ("accept 9: the protocol's checks on what the three chains have read",
      Thunk.mk fun _ => run x (viewOf C D y τ₁ τ₂ τ₃ (rvT C D.ds₁ τ₁) D.key₁ w₁.get)
        (viewOf C D y τ₁ τ₂ τ₃ (rvT C D.ds₂ τ₂) D.key₂ w₂.get)
        (viewOf C D y τ₁ τ₂ τ₃ (rvT C D.ds₃ τ₃) D.key₃ w₃.get))]

variable {I X : Type} {L : BatchProtocolWithLeafBody I X}

/-- The part behind the chain at a whole file, with the decision taken apart. own, listed: where
openings stand in π. (ρ, rts, ph): the chain's value. -/
def wholeSteps (sMT sFS : ℕ)
    (embS : (p : OPos (chainsOf C D tF tJ t3).sh) → OSym (chainsOf C D tF tJ t3).sh p → Body L)
    (embE : SgX → Body L) (depthReq : ℕ) (cms : List (Dig 256)) (x : Xi)
    (π : OneProtocolProof 256 (wholeDesc C D tF tJ t3 silent run).batch) (own : Leaves)
    (listed : List (oneExternalString (2 ^ D.a) SgX).Pos) (g : Rom.Fam (typedOracleFamily 256 (K + 1) L))
    (ρ : Rho (chainsOf C D tF tJ t3).sh) (rts : RootsOfChain 256 (chainsOf C D tF tJ t3).sh)
    (ph : Phase 256) : Steps :=
  behindSteps sMT sFS (wholeDesc C D tF tJ t3 silent run).batch (wiresOf C K chal D tF tJ t3).sh
      (wlOne D.a) (nOpenW D) (maxDepthW D) embS embE depthReq cms x π own listed
      (rdWhole C D tF tJ t3 ρ) (rdEWhole C D tF tJ t3 ρ) g ρ rts ph ++
    acceptSteps C D tF tJ t3 silent run x
      ((wlOne D.a).build fun p => (π.ext p).map _root_.Compile.Opening.sym)
      (mkTr (chainsOf C D tF tJ t3).sh (chainsOf C D tF tJ t3).ann (wiresOf C K chal D tF tJ t3).sh
        rts π.plains ρ π.opens)

end Whole

end OnBytes.Maker
