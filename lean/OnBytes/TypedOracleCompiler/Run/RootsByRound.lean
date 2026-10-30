-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
[RootsFitR: OnBytes/TypedOracleCompiler's Run/PageXAsked.lean declares TypedOracleCompiler.Run.PQ.RootsFit already: the two
files could not be imported into one.] OnBytes/TypedOracleCompiler/Run/RootsByRound.lean: THE ROOTS BY ROUND ARE THE
ROOTS BY NUMBER: D.RtsOk HOLDS AT THE RECORD rtAll THAT chain_whole YIELDS. A joint between the
chain's half and the forests' half of "the tie at H_b" for a proof file (LinkF).
The compiler under OnBytes/TypedOracleCompiler/ is the one that `innerCompiledVerifier` is made with; it builds on
definitions of Compile/.
WHY (the forests' half asks D.RtsOk Rt rts; the chain's half yields rts = rtAll D rtF ros₁ ros₂
ros₃. By the texts they fit; neither half has it). Run/ChainF.lean's chain_whole says what the chain
yields for the roots ROUND BY ROUND (local rounds: the slot's component; shared rounds: the shared
one). Slice/Batch3SWhole.lean's BD.goodAt | Batch3SWholeF's assemble3_checks ask that the roots
which that record holds for the three stretches' trees, COUNTED THROUGH FROM 0 (the front's not
counted), stand under a relation Rt.
THIS IS THE FIRST FILE THAT IMPORTS BOTH HALVES' PIECES.
  RootsFitR ds ros        round by round: as many roots were read as the round has trees
  rootsFit_of_facts      it follows from StretchFacts (FitL: d.trees.length = the entry's roots =
                         the number of root items; the items read are the description's)
  length_rootsD          so a stretch's roots are as many as its trees (Slice/Plain3.lean's nTrees)
  rtsLo_rtJ | rtsSh_rtJ | rtsL_rtSL     one stretch: if the list All, from its n-th place on, begins
                                        with the stretch's roots, then RtsLo | RtsSh | RtsL hold at
                                        "All[n]? = some c", at rtJ … (rtSL | rtShL …) tail | rtSL …
  rtsOk_rtAll        D.RtsOk (fun n c => (rootsD ros₁ ++ (rootsD ros₂ ++ rootsD ros₃))[n]? = some c)
                     (rtAll D rtF ros₁ ros₂ ros₃), under RootsFitR at the three stretches
  rtsOk_of_facts         the same from three StretchFacts
WHAT IS NOT SAID. That tree n's root in that list is the root in which an opening's walk ended
(OwnOk: the reader's roots[n]; for a tree taken over: num's law (not stated here)). The front's root
(rtF) is in the record (rts.1.2) and outside RtsOk: CompGood takes it. Nothing on Same5: rootsD |
  rtAll at the reader's own rounds: Run/StretchRead.lean's rootsD_same, Run/ChainFRead.lean's
  rtAll_same.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Run.ChainFRead
import OnBytes.TypedOracleCompiler.Slice.Batch3SWhole

set_option autoImplicit false

namespace TypedOracleCompiler.Run.PQ
open Rom TypedOracleCompiler.Iop _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Run.Twin
    TypedOracleCompiler.Run.Thin
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run _root_.Run.PQ TypedOracleCompiler.Run
open _root_.Fmt (RoundOut ChainOut Item ItemValue)
open TypedOracleCompiler.Slice (shA BD nTrees RtsLo RtsSh RtsL)

/-- round by round: as many roots were read as the round has trees -/
def RootsFitR : List RD → List RoundOut → Prop
  | [], [] => True
  | d :: ds, ro :: ros => (_root_.Fmt.rootsOf ro.vals).length = d.trees.length ∧ RootsFitR ds ros
  | _, _ => False

theorem rootsFit_of_trace (h : HId) (P : _root_.Fmt.Plan) :
    ∀ (ds : List RD) (rs : List _root_.Fmt.Round) (ros : List RoundOut) (c : _root_.Fmt.Chain)
        (roots : Array ByteArray),
      FitL ds rs → TraceL h P rs ros c roots → RootsFitR ds ros
  | [], [], [], _, _, _, _ => trivial
  | [], [], _ :: _, _, _, _, t => t.elim
  | [], _ :: _, _, _, _, hf, _ => hf.elim
  | _ :: _, [], _, _, _, hf, _ => hf.elim
  | _ :: _, _ :: _, [], _, _, _, t => t.elim
  | d :: ds, r :: rs, ro :: ros, c, roots, hf, t => by
    obtain ⟨-, -, hit, htree, hcount, -, hf'⟩ := hf
    obtain ⟨-, hv, -, -, -, t'⟩ := t
    obtain ⟨p, hp⟩ := ofGots_whole P.field d.items ro.msg ro.vals (by rw [hit]; exact hv)
    exact ⟨by rw [roots_ofGots d.items ro.vals p hp, hit, hcount, htree], rootsFit_of_trace h P ds rs ros _ _ hf' t'⟩

theorem rootsFit_of_facts {O : ByteArray → ByteArray} {P : _root_.Fmt.Plan} {C : CK} {K : ℕ}
    {ds : List RD}
    {rs : List _root_.Fmt.Round} {ros : List RoundOut} {c : _root_.Fmt.Chain}
        {roots : Array ByteArray}
    {pl : Plains (uL C ds)} (F : StretchFacts O P C K ds rs ros c roots pl) : RootsFitR ds ros :=
  rootsFit_of_trace _ P ds rs ros c roots F.fit F.trace

theorem rootsD_cons (ro : RoundOut) (ros : List RoundOut) :
    rootsD (ro :: ros) = (_root_.Fmt.rootsOf ro.vals).map bytesToDig ++ rootsD ros := by
  unfold rootsD
  rw [List.flatMap_cons, List.map_append]

theorem length_rootsD : ∀ (ds : List RD) (ros : List RoundOut), RootsFitR ds ros →
    (rootsD ros).length = nTrees ds
  | [], [], _ => rfl
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim
  | d :: ds, ro :: ros, h => by
      rw [rootsD_cons, List.length_append, List.length_map, h.1, length_rootsD ds ros h.2]
      rfl

section
variable (All : List (Dig 256)) (C : CK) (T : List RS)

/-- one round's roots stand where the list says; what is left of the list behind them -/
theorem round_at (ro : RoundOut) (m n : ℕ) (X : List (Dig 256))
    (hm : (_root_.Fmt.rootsOf ro.vals).length = m)
    (hA : All.drop n = (_root_.Fmt.rootsOf ro.vals).map bytesToDig ++ X) :
    (∀ k c, ((_root_.Fmt.rootsOf ro.vals).map bytesToDig)[k]? = some c → All[n + k]? = some c) ∧
      All.drop (n + m) = X := by
  refine ⟨fun k c hk => ?_, ?_⟩
  · rw [← List.getElem?_drop, hA, List.getElem?_append_left (List.getElem?_eq_some_iff.1 hk).1]
    exact hk
  · rw [← List.drop_drop, hA]
    exact List.drop_left' (by rw [List.length_map]; exact hm)

theorem rtsLo_rtJ (Tl : RootsOfChain 256 (up T) → Prop) (post : List (Dig 256)) (tail : RootsOfChain 256 (up T))
    (hT : Tl tail) :
    ∀ (ds : List RD) (ros : List RoundOut) (n : ℕ), RootsFitR ds ros →
        All.drop n = rootsD ros ++ post →
      RtsLo (fun n c => All[n]? = some c) C T Tl n ds (rtJ C T ds (rtSL C ds ros) tail)
  | [], [], _, _, _ => hT
  | [], _ :: _, _, h, _ => h.elim
  | _ :: _, [], _, h, _ => h.elim
  | d :: ds, ro :: ros, n, h, hA => by
      rw [rootsD_cons, List.append_assoc] at hA
      obtain ⟨a, b⟩ := round_at All ro d.trees.length n _ h.1 hA
      exact ⟨a, rtsLo_rtJ Tl post tail hT ds ros (n + d.trees.length) h.2 b⟩

theorem rtsSh_rtJ (Tl : RootsOfChain 256 (up T) → Prop) (post : List (Dig 256)) (tail : RootsOfChain 256 (up T))
    (hT : Tl tail) :
    ∀ (ds : List RD) (ros : List RoundOut) (n : ℕ), RootsFitR ds ros →
        All.drop n = rootsD ros ++ post →
      RtsSh (fun n c => All[n]? = some c) C T Tl n ds (rtJ C T ds (rtShL C ds ros) tail)
  | [], [], _, _, _ => hT
  | [], _ :: _, _, h, _ => h.elim
  | _ :: _, [], _, h, _ => h.elim
  | d :: ds, ro :: ros, n, h, hA => by
      rw [rootsD_cons, List.append_assoc] at hA
      obtain ⟨a, b⟩ := round_at All ro d.trees.length n _ h.1 hA
      exact ⟨a, rtsSh_rtJ Tl post tail hT ds ros (n + d.trees.length) h.2 b⟩

theorem rtsL_rtSL (post : List (Dig 256)) :
    ∀ (ds : List RD) (ros : List RoundOut) (n : ℕ), RootsFitR ds ros →
        All.drop n = rootsD ros ++ post →
      RtsL (fun n c => All[n]? = some c) C n ds (rtSL C ds ros)
  | [], [], _, _, _ => trivial
  | [], _ :: _, _, h, _ => h.elim
  | _ :: _, [], _, h, _ => h.elim
  | d :: ds, ro :: ros, n, h, hA => by
      rw [rootsD_cons, List.append_assoc] at hA
      obtain ⟨a, b⟩ := round_at All ro d.trees.length n _ h.1 hA
      exact ⟨a, rtsL_rtSL post ds ros (n + d.trees.length) h.2 b⟩

end

/-- RtsOk at the record that chain_whole yields. -/
theorem rtsOk_rtAll (D : BD) (rtF : List (Dig 256)) (ros₁ ros₂ ros₃ : List RoundOut)
    (h₁ : RootsFitR D.G.ds₁ ros₁)
    (h₂ : RootsFitR D.G.ds₂ ros₂) (h₃ : RootsFitR D.G.ds₃ ros₃) :
    D.RtsOk (fun n c => (rootsD ros₁ ++ (rootsD ros₂ ++ rootsD ros₃))[n]? = some c)
        (rtAll D rtF ros₁ ros₂ ros₃) := by
  have l₁ := length_rootsD _ _ h₁
  have l₂ := length_rootsD _ _ h₂
  have d₂ : (rootsD ros₁ ++ (rootsD ros₂ ++ rootsD ros₃)).drop (nTrees D.G.ds₁) = rootsD ros₂ ++
      rootsD ros₃ :=
    List.drop_left' l₁
  have d₃ : (rootsD ros₁ ++ (rootsD ros₂ ++ rootsD ros₃)).drop
      (nTrees D.G.ds₁ + nTrees D.G.ds₂) = rootsD ros₃ ++ [] := by
    rw [← List.drop_drop, d₂, List.append_nil]
    exact List.drop_left' l₂
  exact rtsLo_rtJ _ D.G.C D.SJ _ (rootsD ros₂ ++ rootsD ros₃) _
    (rtsSh_rtJ _ D.G.C D.S₃ _ (rootsD ros₃) _ (rtsL_rtSL _ D.G.C [] D.G.ds₃ ros₃ _ h₃ d₃)
        D.G.ds₂ ros₂ _ h₂ d₂)
    D.G.ds₁ ros₁ 0 h₁ (List.drop_zero)

theorem rtsOk_of_facts (D : BD) (rtF : List (Dig 256)) {O : ByteArray → ByteArray}
    {P₁ P₂ P₃ : _root_.Fmt.Plan} {K : ℕ}
    {rs₁ rs₂ rs₃ : List _root_.Fmt.Round} {ros₁ ros₂ ros₃ : List RoundOut}
        {c₁ c₂ c₃ : _root_.Fmt.Chain}
    {ro₁ ro₂ ro₃ : Array ByteArray} {pl₁ : Plains (uL D.G.C D.G.ds₁)}
        {pl₂ : Plains (uL D.G.C D.G.ds₂)}
    {pl₃ : Plains (uL D.G.C D.G.ds₃)} (F₁ : StretchFacts O P₁ D.G.C K D.G.ds₁ rs₁ ros₁ c₁ ro₁ pl₁)
    (F₂ : StretchFacts O P₂ D.G.C K D.G.ds₂ rs₂ ros₂ c₂ ro₂ pl₂)
    (F₃ : StretchFacts O P₃ D.G.C K D.G.ds₃ rs₃ ros₃ c₃ ro₃ pl₃) :
    D.RtsOk (fun n c => (rootsD ros₁ ++ (rootsD ros₂ ++ rootsD ros₃))[n]? = some c)
        (rtAll D rtF ros₁ ros₂ ros₃) :=
  rtsOk_rtAll D rtF ros₁ ros₂ ros₃ (rootsFit_of_facts F₁) (rootsFit_of_facts F₂)
      (rootsFit_of_facts F₃)

end TypedOracleCompiler.Run.PQ
