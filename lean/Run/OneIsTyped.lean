-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/OneIsTyped.lean: the run of the compiled verifier over a single oracle and its run at typed
oracle functions agree wherever the verifier asks only queries that the encoding can write.

This is the first step towards the theorem of Run/OneIsTypedTop.lean (`one_is_typed`). The compiled
verifier of the generic construction can be run over a single oracle on bit strings, through an
encoding of the queries (`V1C`, `run1C`: Run/PageQRunC.lean), or at one oracle function for each
kind of query, defined from the format page's hash calls (`VPC`, `runLaxC`: Run/PlanQS.lean). Here
the two are shown to agree on every argument string (the proof, as the compiler's theorems type it)
on which the verifier asks nothing outside the description's plan of rounds. The statements hold for
every description S that passes the encoding's test `OKQ S`, and for every choice of challenge
types, number of the sampler's blocks, sampler and decision.

1. What the file contains.
   `fitFb`, `fitLeaf`: The two tests on a query.
   `askedQ`: Every chain query and, where the strict format holds, every leaf query that the
     evaluable form of the compiled verifier (`verifyP`, Run/ThinDefs.lean), at the family read out
     of the single oracle, forms on an argument string passes these tests, and the chain does not
     join (`askedP`, Run/ThinAsked.lean).
   `askedFile`: The same for what the lenient reader (it only splits the file) makes of a file. To
     cut the file, the lenient reader recomputes the hash chain, and it refuses some files (what it
     still asks the hash, what it refuses and what it does not test: part 1 of the head of
     Run/ParseLax.lean).

2. What is checked when the file compiles. Nothing beyond the proofs.

3. Theorems.
   `allBlocks_leaf`, `allBlocks_node`, `allBlocks_fb`: For any encoding C and spellings D that fit
     together (`PageFit C D`, Run/CodingAgree.lean): the family of oracle functions read out of the
     single oracle with all blocks requested (`readBlocks`), compared with `famOf Fmt.oracle D`.
     (`agree` in Run/CodingAgree.lean speaks of `readSome`, where the blocks that the format does
     not write are not requested.)
   `one_asked`; `askedQK_eq`; `one_file`.

4. What is not claimed.
   That the test holds for what the lenient reader makes of a file. That is proved in
   Run/OneIsTypedTop.lean (`asked_of`, `parse_facts`, `fitsS_of`, under `ok S = true`, K + 1 < 2^48
   and three more bounds on numbers).
   The test has not been run. As written it is no test for an evaluator: one trial, on files of a
   description whose rounds draw field elements, ran into the memory limit. It serves as a step of a
   proof.
   No statement on soundness follows.
   Limits: see "To be declared with every use" in the head of Run/ParseBS.lean (`leafSalt`).

Terms: lean/GLOSSARY.md.
-/
import Run.ThinAsked
import Run.CodingAgree
import Run.PageQKeepC
import Run.PlanQS

set_option autoImplicit false

namespace Run
open Rom Compile Compile.Batch Iop

section
variable {I X : Type} {L : BatchProtocol I X} {K : ℕ} {tg : Tag} (C : PageC L K tg) (D : PageD L tg)

/-- For `F : PageFit C D`, at a leaf query that the encoding writes in the format (`h`): the family
read out of the single oracle, all blocks asked, is the typed family. -/
theorem allBlocks_leaf (F : PageFit C D) (q : LeafIn L)
    (h : ((pLeaf C.saltBits C.leafP).put q).isSome = true) :
    (readBlocks (theImpl C) oBits .leaf q : Dig 256) = famOf _root_.Fmt.oracle D K .leaf q :=
  (agree F .leaf q h).symm

theorem allBlocks_node (F : PageFit C D) (q : Bits × Bits)
    (h : ((pNode C.cfg).put q).isSome = true) :
    (readBlocks (theImpl C) oBits .node q : Dig 256) = famOf _root_.Fmt.oracle D K .node q :=
  (agree F .node q h).symm

/-- For `F : PageFit C D`, at a chain query that fits (`h`): one chain value; and one whole answer
if the round is not 0. -/
theorem allBlocks_fb (F : PageFit C D) (q : FbIn 256 L tg) (h : fitsC C (.fb tg) q = true) :
    (readBlocks (theImpl C) oBits (.fb tg) q : (Fin K → Dig 256) × Dig 256).2 =
      (famOf _root_.Fmt.oracle D K (.fb tg) q : (Fin K → Dig 256) × Dig 256).2 ∧
    (q.round ≠ 0 →
      readBlocks (theImpl C) oBits (.fb tg) q = famOf _root_.Fmt.oracle D K (.fb tg) q) := by
  have hq : (if q.round = 0 then (C.first.put q).isSome
        else (List.finRange (K + 1)).all fun j => ((p162 C.chain K).put (q, j)).isSome) = true :=
    (fitsC_fb C q).symm.trans h
  have hlast : needC C (.fb tg) q (Fin.last K) = true := by
    rw [needC_fb]
    by_cases h0 : q.round = 0
    · rw [pFb_zero C q _ h0, if_pos (Fin.val_last K)]
      rw [if_pos h0] at hq
      exact hq
    · rw [pFb_succ C q _ h0]
      rw [if_neg h0, List.all_eq_true] at hq
      exact hq _ (List.mem_finRange _)
  have hA := agree F (.fb tg) q h
  have hS : readSome (theImpl C) (needC C) oBits (.fb tg) q =
      (((fun k : Fin K =>
          if needC C (.fb tg) q k.castSucc = true then
            oBits () ((theImpl C).code (.fb tg) q k.castSucc)
          else dig0 256),
        if needC C (.fb tg) q (Fin.last K) = true then
          oBits () ((theImpl C).code (.fb tg) q (Fin.last K))
        else dig0 256) : (Fin K → Dig 256) × Dig 256) := rfl
  have hB : readBlocks (theImpl C) oBits (.fb tg) q =
      (((fun k : Fin K => oBits () ((theImpl C).code (.fb tg) q k.castSucc)),
        oBits () ((theImpl C).code (.fb tg) q (Fin.last K))) : (Fin K → Dig 256) × Dig 256) := rfl
  refine ⟨?_, fun h0 => ?_⟩
  · rw [hA, hS, hB, if_pos hlast]
  · rw [hA, hS, hB, if_pos hlast]
    congr 1
    funext k
    have hk : needC C (.fb tg) q k.castSucc = true := by
      rw [needC_fb, pFb_succ C q _ h0]
      rw [if_neg h0, List.all_eq_true] at hq
      exact hq _ (List.mem_finRange _)
    rw [if_pos hk]

end

end Run

namespace Run.PQ
open Rom Iop Compile Compile.Batch Run.Thin

section
variable (S : _root_.Fmt.Spec) (C : CK) (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k)
  (dec : View → Bool) (h : OKQ S = true)

/-- The test on a chain query: round 0: the encoding's first code writes it; a later round: the test
that writes no string. -/
def fitFb (q : FbIn 256 (LfQ S C dec ()) .onl) : Bool :=
  if q.round = 0 then ((pageQ S C dec (K + 1) h).first.put q).isSome else fitsQ S C dec (K + 1) q

/-- The test on a leaf query: the encoding writes it in the format. -/
def fitLeaf (q : LeafIn (LfQ S C dec ())) : Bool :=
  ((pLeaf (pageQ S C dec (K + 1) h).saltBits (pageQ S C dec (K + 1) h).leafP).put q).isSome

theorem fitFb_fits (q : FbIn 256 (LfQ S C dec ()) .onl) (hq : fitFb S C K dec h q = true) :
    fitsC (pageQ S C dec (K + 1) h) (.fb .onl) q = true := by
  rw [fitsC_fb]
  unfold fitFb at hq
  by_cases h0 : q.round = 0
  · rw [if_pos h0] at hq ⊢
    exact hq
  · rw [if_neg h0] at hq ⊢
    rw [List.all_eq_true]
    exact fun j _ => fitsQ_put S C dec (K + 1) q hq j

/-- The test on an argument string: `verifyP`, at the family read out of the single oracle, asks
nothing off the plan. -/
def askedQ (cm : Dig 256) (π : OneProtocolProof 256 (PSof C (rds S) dec).up) : Bool :=
  askedP (lam := 256) (K := K + 1) (fun _ => LbS C (rds S) dec) (gQ S C dec (K + 1) h) id none
    (256 + 8 * S.plan.salt) 256 .onl (fitFb S C K dec h) (fitLeaf S C K dec h) (PSof C (rds S) dec)
    (wqS C K chal (rds S) dec) (fun p a => some (.inr ⟨Tag.onl, ⟨p, a⟩⟩)) (embPS C (rds S) dec) some
    (fun s => some (.inl s)) 0 [cm] () π

/-- For `OKQ S = true` (`h`): where that test holds (`ha`), the verifier over the single oracle is
the verifier at the typed oracle functions. -/
theorem one_asked (cm : Dig 256) (π : OneProtocolProof 256 (PSof C (rds S) dec).up)
    (ha : askedQ S C K chal dec h cm π = true) :
    V1C S C K chal dec h cm π = VPC S C K chal dec cm π := by
  have F := pageQ_fit S C dec (K + 1) (Nat.succ_pos K) h
  unfold V1C VPC
  rw [verifyPR_eq, verifyPB_eq, verifyPB_eq, famK_eq, famP_eq]
  have hw : FrontBlind (lam := 256) (K := K + 1) (PSof C (rds S) dec).S
      (PSof C (rds S) dec).ann (wqS C K chal (rds S) dec).sh :=
    fun _ _ => Subsingleton.elim _ _
  refine verifyP_asked (fun _ => LbS C (rds S) dec) _ _ id none _ 256 .onl
    (fitFb S C K dec h) (fitLeaf S C K dec h) ?_ ?_ ?_ (PSof C (rds S) dec)
    (wqS C K chal (rds S) dec) hw _ _ _ _ 0 [cm] () π ha
  · intro q hq
    rw [gQ_eq]
    exact allBlocks_fb _ _ F q (fitFb_fits S C K dec h q hq)
  · intro q hq
    rw [gQ_eq]
    exact allBlocks_leaf _ _ F q hq
  · intro a b
    unfold Thin.nodeP
    rw [gQ_eq]
    refine allBlocks_node _ _ F _ ?_
    rw [pNode_put _ _ _ List.length_ofFn List.length_ofFn]
    rfl

/-- The same test at `gQK`, the family that keeps the hash's state (`askedFile` is stated with it;
`askedQK_eq`: it is `askedQ`). As written it is no test for an evaluator, and it has not been run:
part 4 of the head. -/
def askedQK (cm : Dig 256) (π : OneProtocolProof 256 (PSof C (rds S) dec).up) : Bool :=
  askedP (lam := 256) (K := K + 1) (fun _ => LbS C (rds S) dec) (gQK S C dec (K + 1) h) id none
    (256 + 8 * S.plan.salt) 256 .onl (fitFb S C K dec h) (fitLeaf S C K dec h) (PSof C (rds S) dec)
    (wqS C K chal (rds S) dec) (fun p a => some (.inr ⟨Tag.onl, ⟨p, a⟩⟩)) (embPS C (rds S) dec) some
    (fun s => some (.inl s)) 0 [cm] () π

theorem askedQK_eq (cm : Dig 256) (π : OneProtocolProof 256 (PSof C (rds S) dec).up) :
    askedQK S C K chal dec h cm π = askedQ S C K chal dec h cm π := by
  unfold askedQK askedQ
  rw [gQK_eq S C dec (K + 1) (Nat.succ_pos _) h]

end

/-- The test on a file: on what the lenient reader makes of it the verifier asks nothing off the
plan; true where the reader refuses, and where `OKQ S` fails. -/
def askedFile (S : _root_.Fmt.Spec) (C : CK) (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k)
    (dec : View → Bool) (file : ByteArray) : Bool :=
  if h : OKQ S = true then
    match parseLaxFP (PSof C (rds S) dec) S (TYS S C dec) file with
    | some ([cm], π) => askedQK S C K chal dec h cm π
    | _ => true
  else true

/-- For `OKQ S = true`: the run over the single oracle is the run at the typed oracle functions,
including who decided, on every file that passes the test (`ha`). -/
theorem one_file (S : _root_.Fmt.Spec) (C : CK) (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k)
    (dec : View → Bool) (file : ByteArray) (h : OKQ S = true)
    (ha : askedFile S C K chal dec file = true) :
    run1C S C K chal dec file = runLaxC S C K chal dec file := by
  unfold askedFile at ha
  rw [dif_pos h] at ha
  unfold run1C runLaxC
  rw [← (laxFast_parse _ S _ file).1]
  revert ha
  generalize parseLaxFP (PSof C (rds S) dec) S (TYS S C dec) file = x
  intro ha
  unfold run1COn runOnC
  rw [dif_pos h]
  by_cases hk : ok S = true
  · rw [if_pos hk, if_pos hk]
    match x, ha with
    | none, _ => rfl
    | some ([], _), _ => rfl
    | some ([cm], π), ha => 
      simp only
      rw [one_asked S C K chal dec h cm π ((askedQK_eq S C K chal dec h cm π).symm.trans ha)]
    | some (_ :: _ :: _, _), _ => rfl
  · rw [if_neg hk, if_neg hk]

end Run.PQ
