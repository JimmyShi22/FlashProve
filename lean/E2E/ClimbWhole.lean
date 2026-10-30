-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/ClimbWhole.lean: the protocol of a whole file (`reductionOfWholeFile`, OnBytes/Maker/Whole.lean) is the
protocol at the file's data with every round's proof of work set to 0, with the bits added
(E2E/ClimbPair.lean, E2E/ClimbPairBatch.lean). So round-by-round soundness and knowledge soundness
of the one hold with a list of counts if and only if those of the other do with the same counts.

In `reductionOfWholeFile C D` the proofs of work stand inside the rounds: a round's verifier message is
`GChal work ..`, its plain part `GPlain ℕ work ..`, and the verifier's first three tests are that
all bits are 0. `noWork D` is D with `work := 0` in every round of the three chains. The tests on
what the three single rounds send (`silent`) and the decision on the three views (`run`) are the
same letters on both sides: they see views, in which neither nonce nor bits occur. A nonce and bits
stand in the rounds with work > 0 alone; the other rounds are the same on both sides.

What "without proof of work" means here. The data at `work := 0` give the typed rounds: no nonce, no
bits. The decisions are the SAME FUNCTIONS on both sides. Where such a function is itself made from
a written text of the protocol, that text is not rewritten: it may still declare the bits and hold
its entries against a list of rounds with the bits; the function sees views alone, in which neither
nonce nor bits occur, so no statement here suffers. That the protocol's text, rewritten at 0 bits,
gives this protocol is shown nowhere.

Why a pair of maps and not an equation `reductionOfWholeFile C D = (reductionOfWholeFile C (noWork D)).grind g`:
  * `IOR` has no `grind`; it could be said of `toInteractiveOracleProof` alone;
  * for a kit C in general the types `C.Ch e k` and `C.Ch (entry0 e) k` are not the same
    (`KitFree`, E2E/ClimbChain.lean, asks for a bijection);
  * the lists of rounds are equal by a proof by induction, not by unfolding, so that an equation of
    protocols would need casts in four fields;
  * the fields `reads` and `accept` are written differently and are equal by a proof only.
Soundness reads the list of rounds and `accept` alone, and the pair has no cast.

Main names:
  `rdt0`, `noWork`: a round's data, a file's data, with no proof of work.
  `pairT`, `bitsT`: a chain's pair and its numbers of bits.
  `pairW`, `bitsW`, `pairW_bits`: the same for the whole file.
  `whole_accept`: the verifier accepts exactly if all proof-of-work bits are 0 and the verifier
    without proof of work accepts the stripped transcript.
  `wholePair`, `wholeBatchPair`: the pairs of the protocols, plain and with the file's annotation.
  `whole_sound_iff`: round-by-round soundness, both ways. (Knowledge soundness of the file as a
    batch: `BatchPair.sndBKT_iff` at `wholeBatchPair`.)

Limits. Acceptance and soundness alone: nothing on queries (`reads`, `extReads` are not compared),
completeness or zero knowledge. D, `silent`, `run` are free letters. Nothing says that any list of
counts is small.

"Without proof of work" is a reading of this folder's writers: the same rounds' data with the number
of proof-of-work bits set to 0, under the same decision functions. Whether that protocol may stand
for "the IOP without proof of work" is an open question, which no theorem here settles.

This file's definitions may be read as part of a goal: they fix the protocol of which the clauses of
E2E/ClimbFiles.lean are stated. They count as none.




-/
import E2E.ClimbChain
import E2E.ClimbThree
import OnBytes.Maker.Whole

set_option autoImplicit false

noncomputable section

namespace AtPublicFiles.Climb
open Iop Prob
open OnBytes.Maker
open Compile.Joined (plainRound)
open _root_.Run.PQ (CK View SgX)

/-! ## 1. Data without proof of work -/

/-- A round's data, with the committed tables that are opened behind it, with no proof of work. -/
def rdt0 (d : RDT) : RDT := ⟨rd0 d.toRD, d.stored⟩

/-- A file's data with no proof of work. -/
def noWork (D : WholeD) : WholeD :=
  ⟨D.a, D.ds₁.map rdt0, D.ds₂.map rdt0, D.ds₃.map rdt0, D.key₁, D.key₂, D.key₃⟩

def z0T : (ds : List RDT) → Z0 (toRDs (ds.map rdt0)) (toRDs ds)
  | [] => .nil
  | d :: ds => .cons d.toRD (z0T ds)

theorem wantsOf_rdt0 (a : ℕ) (dep : ℕ → Option ℕ) :
    ∀ (ds : List RDT) (Rs : List _root_.Fmt.Drawn),
      wantsOf a dep (ds.map rdt0) Rs = wantsOf a dep ds Rs
  | [], _ => rfl
  | _ :: _, [] => rfl
  | _ :: ds, _ :: Rs => congrArg (fun t => _ ++ t) (wantsOf_rdt0 a dep ds Rs)

theorem fullOf_rdt0 :
    ∀ (ds : List RDT) (Rs : List _root_.Fmt.Drawn), fullOf (ds.map rdt0) Rs = fullOf ds Rs
  | [], _ => rfl
  | _ :: _, [] => rfl
  | _ :: ds, _ :: Rs => congrArg (fun t => _ && t) (fullOf_rdt0 ds Rs)

theorem sum_rdt0 : ∀ ds : List RDT,
    ((ds.map rdt0).map (·.trees.length)).sum = (ds.map (·.trees.length)).sum
  | [] => rfl
  | d :: ds => congrArg (fun t => d.trees.length + t) (sum_rdt0 ds)

theorem treeShT_rdt0 (ds : List RDT) (n : ℕ) : treeShT (ds.map rdt0) n = treeShT ds n :=
  treeSh_z0 (z0T ds) n

theorem t₁_noWork (D : WholeD) : (noWork D).t₁ = D.t₁ := sum_rdt0 D.ds₁
theorem t₂_noWork (D : WholeD) : (noWork D).t₂ = D.t₂ := sum_rdt0 D.ds₂

theorem depth_noWork (D : WholeD) : (noWork D).depth = D.depth := by
  funext j
  show (if j < (noWork D).t₁ then (treeShT (D.ds₁.map rdt0) j).map (·.a)
      else if j - (noWork D).t₁ < (noWork D).t₂ then
        (treeShT (D.ds₂.map rdt0) (j - (noWork D).t₁)).map (·.a)
      else (treeShT (D.ds₃.map rdt0) (j - (noWork D).t₁ - (noWork D).t₂)).map (·.a)) =
    if j < D.t₁ then (treeShT D.ds₁ j).map (·.a)
      else if j - D.t₁ < D.t₂ then (treeShT D.ds₂ (j - D.t₁)).map (·.a)
      else (treeShT D.ds₃ (j - D.t₁ - D.t₂)).map (·.a)
  rw [t₁_noWork, t₂_noWork, treeShT_rdt0, treeShT_rdt0, treeShT_rdt0]

/-! ## 2. A chain -/

variable (C : CK) (K : KitFree C)

/-- A chain's rounds are its rounds without proof of work, with the bits added. -/
def pairT (ds : List RDT) : Pair (uLT C (ds.map rdt0)) (uLT C ds) := pairZ C K (z0T ds)

/-- A chain's numbers of proof-of-work bits. -/
def bitsT (ds : List RDT) : GBits (uLT C (ds.map rdt0)) := bitsZ C (z0T ds)

theorem pairT_bits (ds : List RDT) : (pairT C K ds).toEmb.Bits (bitsT C ds) :=
  pairZ_bits C K (z0T ds)

/-- All proof-of-work checks of a chain's part of a transcript. -/
def Pof (ds : List RDT) (τ : Tr (uLT C ds)) : Bool := passT C ds (rhoT C ds τ)

/-- What was sampled in a chain's part of a transcript. -/
def Rof (ds : List RDT) (τ : Tr (uLT C ds)) : List _root_.Fmt.Drawn := drawnT C ds (rhoT C ds τ)

/-- What the sampled positions of a chain ask for. -/
def Wof (D : WholeD) (ds : List RDT) (τ : Tr (uLT C ds)) : List Want :=
  wantsOf D.a D.depth ds (Rof C ds τ)

theorem Pof_pair (ds : List RDT) (τ : Tr (uLT C ds)) : (pairT C K ds).passTr τ = Pof C ds τ :=
  pass_pairZ C K (z0T ds) τ

theorem Pof_zero (ds : List RDT) (τ : Tr (uLT C (ds.map rdt0))) : Pof C (ds.map rdt0) τ = true :=
  pass_zero C (z0T ds) _

theorem Rof_strip (ds : List RDT) (τ : Tr (uLT C ds)) :
    Rof C (ds.map rdt0) ((pairT C K ds).strip τ) = Rof C ds τ :=
  drawn_strip C K (z0T ds) τ

theorem rvT_strip (ds : List RDT) (τ : Tr (uLT C ds)) :
    rvT C (ds.map rdt0) ((pairT C K ds).strip τ) = rvT C ds τ :=
  rv_strip C K (z0T ds) τ

theorem colAt_strip (ds : List RDT) (τ : Tr (uLT C ds)) (n x : ℕ) :
    colAtST C (ds.map rdt0) ((pairT C K ds).strip τ) n x = colAtST C ds τ n x :=
  col_strip C K (z0T ds) τ n x

theorem full_strip (ds : List RDT) (τ : Tr (uLT C ds)) :
    fullOf (ds.map rdt0) (Rof C (ds.map rdt0) ((pairT C K ds).strip τ)) = fullOf ds (Rof C ds τ) :=
  (congrArg (fullOf (ds.map rdt0)) (Rof_strip C K ds τ)).trans (fullOf_rdt0 ds _)

theorem Wof_strip (D : WholeD) (ds : List RDT) (τ : Tr (uLT C ds)) :
    Wof C (noWork D) (ds.map rdt0) ((pairT C K ds).strip τ) = Wof C D ds τ :=
  (congrArg (wantsOf D.a (noWork D).depth (ds.map rdt0)) (Rof_strip C K ds τ)).trans
    ((congrArg (fun dp => wantsOf D.a dp (ds.map rdt0) (Rof C ds τ)) (depth_noWork D)).trans
      (wantsOf_rdt0 D.a D.depth ds _))

/-! ## 3. The three views -/

section
variable (D : WholeD) (y : (oneExternalString (2 ^ D.a) SgX).Str) (τ₁ : Tr (uLT C D.ds₁))
  (τ₂ : Tr (uLT C D.ds₂)) (τ₃ : Tr (uLT C D.ds₃))

theorem colOf_strip : ∀ w : Want,
    colOf C (noWork D) y ((pairT C K D.ds₁).strip τ₁) ((pairT C K D.ds₂).strip τ₂)
        ((pairT C K D.ds₃).strip τ₃) w =
      colOf C D y τ₁ τ₂ τ₃ w
  | .table _ _ => rfl
  | .tree j x => by
      show (if j < (noWork D).t₁ then
            colAtST C (D.ds₁.map rdt0) ((pairT C K D.ds₁).strip τ₁) j x
          else if j - (noWork D).t₁ < (noWork D).t₂ then
            colAtST C (D.ds₂.map rdt0) ((pairT C K D.ds₂).strip τ₂) (j - (noWork D).t₁) x
          else colAtST C (D.ds₃.map rdt0) ((pairT C K D.ds₃).strip τ₃)
            (j - (noWork D).t₁ - (noWork D).t₂) x) =
        if j < D.t₁ then colAtST C D.ds₁ τ₁ j x
          else if j - D.t₁ < D.t₂ then colAtST C D.ds₂ τ₂ (j - D.t₁) x
          else colAtST C D.ds₃ τ₃ (j - D.t₁ - D.t₂) x
      rw [t₁_noWork, t₂_noWork, colAt_strip, colAt_strip, colAt_strip]

theorem viewOf_strip (rs : List _root_.Fmt.RoundView) (key : ℕ → ℕ) (ws : List Want) :
    viewOf C (noWork D) y ((pairT C K D.ds₁).strip τ₁) ((pairT C K D.ds₂).strip τ₂)
        ((pairT C K D.ds₃).strip τ₃) rs key ws =
      viewOf C D y τ₁ τ₂ τ₃ rs key ws := by
  have hc : colOf C (noWork D) y ((pairT C K D.ds₁).strip τ₁) ((pairT C K D.ds₂).strip τ₂)
      ((pairT C K D.ds₃).strip τ₃) = colOf C D y τ₁ τ₂ τ₃ :=
    funext (colOf_strip C K D y τ₁ τ₂ τ₃)
  unfold viewOf
  rw [hc]

end

/-! ## 4. The verifier's decision -/

section
variable {Xi TF TJ T3 : Type} (silent : Xi → TF → TJ → T3 → Bool)
  (run : Xi → View → View → View → Bool)

/-- The decision of `reductionOfWholeFile`, from its parts. -/
def okOf (x : Xi) (p₁ p₂ p₃ f₁ f₂ f₃ cr : Bool) (a : TF) (b : TJ) (c : T3) (V₁ V₂ V₃ : View) :
    Bool :=
  p₁ && p₂ && p₃ && f₁ && f₂ && f₃ && cr && silent x a b c && run x V₁ V₂ V₃

theorem okOf_congr (x : Xi) (a : TF) (b : TJ) (c : T3)
    {p₁ p₂ p₃ f₁ f₂ f₃ cr p₁' p₂' p₃' f₁' f₂' f₃' cr' : Bool} {V₁ V₂ V₃ V₁' V₂' V₃' : View}
    (h₁ : p₁ = p₁') (h₂ : p₂ = p₂') (h₃ : p₃ = p₃') (h₄ : f₁ = f₁') (h₅ : f₂ = f₂')
    (h₆ : f₃ = f₃') (h₇ : cr = cr') (h₈ : V₁ = V₁') (h₉ : V₂ = V₂') (h₀ : V₃ = V₃') :
    okOf silent run x p₁ p₂ p₃ f₁ f₂ f₃ cr a b c V₁ V₂ V₃ =
      okOf silent run x p₁' p₂' p₃' f₁' f₂' f₃' cr' a b c V₁' V₂' V₃' := by
  rw [h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₀]

/-- The three proof-of-work checks taken out in front. -/
theorem okOf_pass (x : Xi) (p₁ p₂ p₃ f₁ f₂ f₃ cr : Bool) (a : TF) (b : TJ) (c : T3)
    (V₁ V₂ V₃ : View) :
    okOf silent run x p₁ p₂ p₃ f₁ f₂ f₃ cr a b c V₁ V₂ V₃ =
      ((p₁ && (p₂ && p₃)) && okOf silent run x true true true f₁ f₂ f₃ cr a b c V₁ V₂ V₃) := by
  cases p₁ <;> cases p₂ <;> cases p₃ <;> rfl

/-- The decision, from the three chains' parts of a transcript and what the three single rounds
send. -/
def okAt (D : WholeD) (x : Xi) (y : (oneExternalString (2 ^ D.a) SgX).Str) (τ₁ : Tr (uLT C D.ds₁))
    (τ₂ : Tr (uLT C D.ds₂)) (τ₃ : Tr (uLT C D.ds₃)) (a : TF) (b : TJ) (c : T3) : Bool :=
  okOf silent run x (Pof C D.ds₁ τ₁) (Pof C D.ds₂ τ₂) (Pof C D.ds₃ τ₃)
    (fullOf D.ds₁ (Rof C D.ds₁ τ₁)) (fullOf D.ds₂ (Rof C D.ds₂ τ₂)) (fullOf D.ds₃ (Rof C D.ds₃ τ₃))
    (carriesOf D y (Wof C D D.ds₁ τ₁ ++ (Wof C D D.ds₂ τ₂ ++ Wof C D D.ds₃ τ₃))) a b c
    (viewOf C D y τ₁ τ₂ τ₃ (rvT C D.ds₁ τ₁) D.key₁ (Wof C D D.ds₁ τ₁))
    (viewOf C D y τ₁ τ₂ τ₃ (rvT C D.ds₂ τ₂) D.key₂ (Wof C D D.ds₂ τ₂))
    (viewOf C D y τ₁ τ₂ τ₃ (rvT C D.ds₃ τ₃) D.key₃ (Wof C D D.ds₃ τ₃))

theorem isSome_ite (b : Bool) :
    (if b = true then some () else (none : Option Unit)).isSome = b := by
  cases b <;> rfl

/-- It is `reductionOfWholeFile`'s. -/
theorem accept_is (D : WholeD) (tF : TF) (tJ : TJ) (t3 : T3) (x : Xi)
    (y : (oneExternalString (2 ^ D.a) SgX).Str) (τ : Tr (chainsOf C D tF tJ t3).sh) :
    (reductionOfWholeFile C D tF tJ t3 silent run).toInteractiveOracleProof.accept x y τ =
      okAt C silent run D x y ((chainsOf C D tF tJ t3).tr₁ τ) ((chainsOf C D tF tJ t3).tr₂ τ)
        ((chainsOf C D tF tJ t3).tr₃ τ) ((chainsOf C D tF tJ t3).msgF τ).2
        ((chainsOf C D tF tJ t3).msgJ τ).2 ((chainsOf C D tF tJ t3).msg3 τ).2 :=
  isSome_ite _

/-- The decision is: the three chains' proof-of-work checks, and the decision without proof of work
at the stripped parts. -/
theorem okAt_strip (D : WholeD) (x : Xi) (y : (oneExternalString (2 ^ D.a) SgX).Str) (τ₁ : Tr (uLT C D.ds₁))
    (τ₂ : Tr (uLT C D.ds₂)) (τ₃ : Tr (uLT C D.ds₃)) (a : TF) (b : TJ) (c : T3) :
    okAt C silent run D x y τ₁ τ₂ τ₃ a b c =
      ((Pof C D.ds₁ τ₁ && (Pof C D.ds₂ τ₂ && Pof C D.ds₃ τ₃)) &&
        okAt C silent run (noWork D) x y ((pairT C K D.ds₁).strip τ₁)
          ((pairT C K D.ds₂).strip τ₂) ((pairT C K D.ds₃).strip τ₃) a b c) := by
  have h : okAt C silent run (noWork D) x y ((pairT C K D.ds₁).strip τ₁)
      ((pairT C K D.ds₂).strip τ₂) ((pairT C K D.ds₃).strip τ₃) a b c =
      okOf silent run x true true true
        (fullOf D.ds₁ (Rof C D.ds₁ τ₁)) (fullOf D.ds₂ (Rof C D.ds₂ τ₂))
        (fullOf D.ds₃ (Rof C D.ds₃ τ₃))
        (carriesOf D y (Wof C D D.ds₁ τ₁ ++ (Wof C D D.ds₂ τ₂ ++ Wof C D D.ds₃ τ₃))) a b c
        (viewOf C D y τ₁ τ₂ τ₃ (rvT C D.ds₁ τ₁) D.key₁ (Wof C D D.ds₁ τ₁))
        (viewOf C D y τ₁ τ₂ τ₃ (rvT C D.ds₂ τ₂) D.key₂ (Wof C D D.ds₂ τ₂))
        (viewOf C D y τ₁ τ₂ τ₃ (rvT C D.ds₃ τ₃) D.key₃ (Wof C D D.ds₃ τ₃)) :=
    okOf_congr silent run x a b c (Pof_zero C D.ds₁ _) (Pof_zero C D.ds₂ _)
      (Pof_zero C D.ds₃ _) (full_strip C K D.ds₁ τ₁)
      (full_strip C K D.ds₂ τ₂) (full_strip C K D.ds₃ τ₃)
      (congrArg (carriesOf D y) (congrArg₂ (· ++ ·) (Wof_strip C K D D.ds₁ τ₁)
        (congrArg₂ (· ++ ·) (Wof_strip C K D D.ds₂ τ₂) (Wof_strip C K D D.ds₃ τ₃))))
      ((viewOf_strip C K D y τ₁ τ₂ τ₃ _ _ _).trans
        (congrArg₂ (fun rs ws => viewOf C D y τ₁ τ₂ τ₃ rs D.key₁ ws) (rvT_strip C K D.ds₁ τ₁)
          (Wof_strip C K D D.ds₁ τ₁)))
      ((viewOf_strip C K D y τ₁ τ₂ τ₃ _ _ _).trans
        (congrArg₂ (fun rs ws => viewOf C D y τ₁ τ₂ τ₃ rs D.key₂ ws) (rvT_strip C K D.ds₂ τ₂)
          (Wof_strip C K D D.ds₂ τ₂)))
      ((viewOf_strip C K D y τ₁ τ₂ τ₃ _ _ _).trans
        (congrArg₂ (fun rs ws => viewOf C D y τ₁ τ₂ τ₃ rs D.key₃ ws) (rvT_strip C K D.ds₃ τ₃)
          (Wof_strip C K D D.ds₃ τ₃)))
  rw [h]
  exact okOf_pass silent run x _ _ _ _ _ _ _ a b c _ _ _

/-! ## 5. The whole file -/

variable (D : WholeD) (tF : TF) (tJ : TJ) (t3 : T3)

/-- The file's rounds are its rounds without proof of work, with the bits added. -/
def pairW : Pair (chainsOf C (noWork D) tF tJ t3).sh (chainsOf C D tF tJ t3).sh :=
  pair3 (plainRound TF tF) (plainRound TJ tJ) (plainRound T3 t3) (pairT C K D.ds₁)
    (pairT C K D.ds₂) (pairT C K D.ds₃)

/-- The file's numbers of proof-of-work bits: 0 at the front round, the joining round and the
seam. -/
def bitsW : GBits (chainsOf C (noWork D) tF tJ t3).sh :=
  bits3 (plainRound TF tF) (plainRound TJ tJ) (plainRound T3 t3) (bitsT C D.ds₁) (bitsT C D.ds₂)
    (bitsT C D.ds₃)

theorem pairW_bits : (pairW C K D tF tJ t3).toEmb.Bits (bitsW C D tF tJ t3) :=
  pair3_bits _ _ _ (pairT_bits C K D.ds₁) (pairT_bits C K D.ds₂) (pairT_bits C K D.ds₃)

/-- **The file's verifier accepts exactly if all proof-of-work bits are 0 and the verifier without
proof of work accepts the transcript with nonces and bits removed.** -/
theorem whole_accept (x : Xi) (y : (oneExternalString (2 ^ D.a) SgX).Str)
    (τ : Tr (chainsOf C D tF tJ t3).sh) :
    (reductionOfWholeFile C D tF tJ t3 silent run).toInteractiveOracleProof.accept x y τ =
      ((pairW C K D tF tJ t3).passTr τ &&
        (reductionOfWholeFile C (noWork D) tF tJ t3 silent run).toInteractiveOracleProof.accept x y
          ((pairW C K D tF tJ t3).strip τ)) := by
  have h₁ : (chainsOf C (noWork D) tF tJ t3).tr₁ ((pairW C K D tF tJ t3).strip τ) =
      (pairT C K D.ds₁).strip ((chainsOf C D tF tJ t3).tr₁ τ) := pair3_tr₁ _ _ _ _ _ _ τ
  have h₂ : (chainsOf C (noWork D) tF tJ t3).tr₂ ((pairW C K D tF tJ t3).strip τ) =
      (pairT C K D.ds₂).strip ((chainsOf C D tF tJ t3).tr₂ τ) := pair3_tr₂ _ _ _ _ _ _ τ
  have h₃ : (chainsOf C (noWork D) tF tJ t3).tr₃ ((pairW C K D tF tJ t3).strip τ) =
      (pairT C K D.ds₃).strip ((chainsOf C D tF tJ t3).tr₃ τ) := pair3_tr₃ _ _ _ _ _ _ τ
  have hF : (chainsOf C (noWork D) tF tJ t3).msgF ((pairW C K D tF tJ t3).strip τ) =
      (chainsOf C D tF tJ t3).msgF τ := pair3_msgF _ _ _ _ _ _ τ
  have hJ : (chainsOf C (noWork D) tF tJ t3).msgJ ((pairW C K D tF tJ t3).strip τ) =
      (chainsOf C D tF tJ t3).msgJ τ := pair3_msgJ _ _ _ _ _ _ τ
  have h3 : (chainsOf C (noWork D) tF tJ t3).msg3 ((pairW C K D tF tJ t3).strip τ) =
      (chainsOf C D tF tJ t3).msg3 τ := pair3_msg3 _ _ _ _ _ _ τ
  have hp : (pairW C K D tF tJ t3).passTr τ =
      (Pof C D.ds₁ ((chainsOf C D tF tJ t3).tr₁ τ) &&
        (Pof C D.ds₂ ((chainsOf C D tF tJ t3).tr₂ τ) &&
          Pof C D.ds₃ ((chainsOf C D tF tJ t3).tr₃ τ))) :=
    (pair3_pass _ _ _ _ _ _ τ).trans (congrArg₂ (· && ·) (Pof_pair C K D.ds₁ _)
      (congrArg₂ (· && ·) (Pof_pair C K D.ds₂ _) (Pof_pair C K D.ds₃ _)))
  rw [accept_is C silent run D tF tJ t3 x y τ,
    accept_is C silent run (noWork D) tF tJ t3 x y ((pairW C K D tF tJ t3).strip τ),
    h₁, h₂, h₃, hF, hJ, h3, hp]
  exact okAt_strip C K silent run D x y _ _ _ _ _ _

/-- **The protocol of the file is the protocol of the file without proof of work, with the bits
added.** -/
def wholePair : ProtoPair (E := oneExternalString (2 ^ D.a) SgX)
    (reductionOfWholeFile C (noWork D) tF tJ t3 silent run).toInteractiveOracleProof
    (reductionOfWholeFile C D tF tJ t3 silent run).toInteractiveOracleProof :=
  ⟨pairW C K D tF tJ t3, whole_accept C K silent run D tF tJ t3⟩

/-- The same with the file's annotation. -/
def wholeBatchPair : BatchPair (E := oneExternalString (2 ^ D.a) SgX)
    ⟨(reductionOfWholeFile C (noWork D) tF tJ t3 silent run).toInteractiveOracleProof, (chainsOf C (noWork D) tF tJ t3).ann⟩
    ⟨(reductionOfWholeFile C D tF tJ t3 silent run).toInteractiveOracleProof, (chainsOf C D tF tJ t3).ann⟩ :=
  ⟨bpair3 (plainRound TF tF) (plainRound TJ tJ) (plainRound T3 t3) (pairT C K D.ds₁)
      (pairT C K D.ds₂) (pairT C K D.ds₃), fun x y τ =>
    (whole_accept C K silent run D tF tJ t3 x y τ).trans
      (congrArg (fun p : Pair (chainsOf C (noWork D) tF tJ t3).sh (chainsOf C D tF tJ t3).sh =>
          (p.passTr τ && (reductionOfWholeFile C (noWork D) tF tJ t3 silent run).toInteractiveOracleProof.accept x y
            (p.strip τ)))
        (toPair_bpair3 (plainRound TF tF) (plainRound TJ tJ) (plainRound T3 t3) (pairT C K D.ds₁)
          (pairT C K D.ds₂) (pairT C K D.ds₃)).symm)⟩

/-- Behind `wholeBatchPair` is `pairW`. -/
theorem wholeBatchPair_toPair :
    (wholeBatchPair C K silent run D tF tJ t3).pair.toPair = pairW C K D tF tJ t3 :=
  toPair_bpair3 _ _ _ _ _ _

/-- **A whole file, round-by-round soundness, both ways**: the protocol without proof of work is
sound with the counts ε if and only if the protocol with proof of work is, for the same language,
with the same counts. -/
theorem whole_sound_iff (L : Xi → (oneExternalString (2 ^ D.a) SgX).Str → Prop)
    (ε : Err (chainsOf C (noWork D) tF tJ t3).sh) :
    (reductionOfWholeFile C (noWork D) tF tJ t3 silent run).toInteractiveOracleProof.Sound L ε ↔
      (reductionOfWholeFile C D tF tJ t3 silent run).toInteractiveOracleProof.Sound L ((pairW C K D tF tJ t3).down ε) :=
  (wholePair C K silent run D tF tJ t3).sound_iff L ε

end

end AtPublicFiles.Climb

#print axioms AtPublicFiles.Climb.whole_accept
#print axioms AtPublicFiles.Climb.wholePair
#print axioms AtPublicFiles.Climb.wholeBatchPair
#print axioms AtPublicFiles.Climb.pairW_bits
#print axioms AtPublicFiles.Climb.whole_sound_iff
