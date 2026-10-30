-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/ClimbLink.lean: the twin of E2E/ClimbWhole.lean at the link: the written link over letters
(`linkProtocolOfRoundData`, OnBytes/Flat/LinkSib.lean) is the link at rounds' data with every round's proof of work
set to 0, with the bits added.

`linkProtocolOfRoundData C ds a xs dec` has one round in front (one verifier message, nothing sent) and then the typed
rounds of ds; its verifier tests that all proof-of-work bits are 0, two tests of format on what was
sampled, and then the decision `dec` on a view. `dec` is the same letter on both sides.

What "without proof of work" means here. The data at `work := 0` give the typed rounds: no nonce, no
bits. The decisions are the SAME FUNCTIONS on both sides. Where such a function is itself made from
a written text of the protocol, that text is not rewritten: it may still declare the bits and hold
its entries against a list of rounds with the bits; the function sees views alone, in which neither
nonce nor bits occur, so no statement here suffers. That the protocol's text, rewritten at 0 bits,
gives this protocol is shown nowhere.

Main names:
  `wantedX_z0`, `carriesX_z0`, `viewX_strip`: what the sampled positions ask for, the test on the
    symbols read of the two committed tables, and the view, are the same without proof of work.
  `pairL`, `bitsL`, `pairL_bits`: the pair, the numbers of bits (0 at the round in front).
  `link_accept`: the verifier accepts exactly if all proof-of-work bits are 0 and the verifier
    without proof of work accepts the stripped transcript.
  `bpairL`, `toPair_bpairL`: the pair that fits the link's annotation (local rounds only).
  `linkPair`, `linkBatchPair`; `link_sound_iff`: the law at the link, both ways.
  `link_accepts_iff`: the link without proof of work accepts some transcript if and only if the link
    does.

Limits: those of E2E/ClimbWhole.lean.

"Without proof of work" is a reading of this folder's writers: the same rounds' data with the number
of proof-of-work bits set to 0, under the same decision functions. Whether that protocol may stand
for "the IOP without proof of work" is an open question, which no theorem here settles.




-/
import E2E.ClimbChain
import E2E.ClimbThree
import OnBytes.Flat.LinkSib

set_option autoImplicit false

noncomputable section

namespace AtPublicFiles.Climb
open Iop Prob
open TypedOracleCompiler.Run.PQ (RD roundS SL SOf uL drawnSL passSL rhoSL rvSL colAtS treeSh wantedXL
  wantedX xWanted symbolsCarryTheirPositions viewX)
open _root_.Run.PQ (CK View SgX XO everyOpeningHasItsDraws s0)
open OnBytes.Flat (linkProtocolOfRoundData)

/-! ## 1. What the sampled positions ask for -/

theorem wantedXL_z0 (a : ℕ) (xs : List XO) {all₀ all : List RD} (h : treeSh all₀ = treeSh all) :
    ∀ {l₀ l : List RD} (_ : Z0 l₀ l) (i : ℕ) (Ds : List _root_.Fmt.Drawn),
      wantedXL a all₀ xs i l₀ Ds = wantedXL a all xs i l Ds
  | _, _, .nil, _, _ => rfl
  | _, _, .cons _ _, _, [] => rfl
  | _, _, .cons (l₀ := l₀) (l := l) d z, i, D :: Ds => by
      show (_ ++ (d.opens.flatMap fun n =>
            (match treeSh all₀ n with
            | none => []
            | some s => (_root_.Fmt.listOf (D.poss.map (· % 2 ^ s.a))).map fun x => (n, x) :
              List (ℕ × ℕ)))) ++
          wantedXL a all₀ xs (i + 1) l₀ Ds =
        (_ ++ (d.opens.flatMap fun n =>
            (match treeSh all n with
            | none => []
            | some s => (_root_.Fmt.listOf (D.poss.map (· % 2 ^ s.a))).map fun x => (n, x) :
              List (ℕ × ℕ)))) ++
          wantedXL a all xs (i + 1) l Ds
      rw [h, wantedXL_z0 a xs h z (i + 1) Ds]

theorem wantedX_z0 (a : ℕ) (xs : List XO) {l₀ l : List RD} (z : Z0 l₀ l)
    (Ds : List _root_.Fmt.Drawn) : wantedX a l₀ xs Ds = wantedX a l xs Ds :=
  wantedXL_z0 a xs (funext (treeSh_z0 z)) z 0 Ds

theorem carriesX_z0 (a : ℕ) (xs : List XO) {l₀ l : List RD} (z : Z0 l₀ l)
    (Ds : List _root_.Fmt.Drawn) (y : (twoExternalStrings (2 ^ a) SgX).Str) :
    symbolsCarryTheirPositions a l₀ xs Ds y = symbolsCarryTheirPositions a l xs Ds y := by
  unfold symbolsCarryTheirPositions xWanted
  rw [wantedX_z0 a xs z Ds]

variable (C : CK) (K : KitFree C)

theorem viewX_strip (a : ℕ) (xs : List XO) {l₀ l : List RD} (z : Z0 l₀ l)
    (y : (twoExternalStrings (2 ^ a) SgX).Str) (τ : Tr (uL C l)) :
    viewX C l₀ a xs y ((pairZ C K z).strip τ) = viewX C l a xs y τ := by
  have hc : colAtS C l₀ ((pairZ C K z).strip τ) = colAtS C l τ :=
    funext fun n => funext fun x => col_strip C K z τ n x
  unfold viewX
  rw [rv_strip C K z τ, drawn_strip C K z τ, hc, wantedX_z0 a xs z]

/-! ## 2. The link -/

section
variable (ds : List RD) (a : ℕ) (xs : List XO) {X : Type} (dec : X → View → Bool)

/-- The link's rounds are its rounds without proof of work, with the bits added. -/
def pairL : Pair (_root_.Run.Twin.up (SOf C (ds.map rd0))) (_root_.Run.Twin.up (SOf C ds)) :=
  Pair.cons (s0 C).up (pairZ C K (z0 ds))

/-- The link's numbers of proof-of-work bits: 0 at the round in front. -/
def bitsL : GBits (_root_.Run.Twin.up (SOf C (ds.map rd0))) := (0, bitsZ C (z0 ds))

theorem pairL_bits : (pairL C K ds).toEmb.Bits (bitsL C ds) :=
  Pair.cons_bits (s0 C).up (pairZ_bits C K (z0 ds))

/-- **The link's verifier accepts exactly if all proof-of-work bits are 0 and the verifier without
proof of work accepts the transcript with nonces and bits removed.** -/
theorem link_accept (x : X) (y : (twoExternalStrings (2 ^ a) SgX).Str)
    (τ : Tr (_root_.Run.Twin.up (SOf C ds))) :
    (linkProtocolOfRoundData C ds a xs dec).accept x y τ =
      ((pairL C K ds).passTr τ &&
        (linkProtocolOfRoundData C (ds.map rd0) a xs dec).accept x y ((pairL C K ds).strip τ)) := by
  obtain ⟨m, c, τ⟩ := τ
  show (passSL C ds (rhoSL C ds τ) && everyOpeningHasItsDraws xs (drawnSL C ds (rhoSL C ds τ)) &&
        symbolsCarryTheirPositions a ds xs (drawnSL C ds (rhoSL C ds τ)) y && dec x (viewX C ds a xs y τ)) =
      ((pairZ C K (z0 ds)).passTr τ &&
        (passSL C (ds.map rd0) (rhoSL C (ds.map rd0) ((pairZ C K (z0 ds)).strip τ)) &&
          everyOpeningHasItsDraws xs (drawnSL C (ds.map rd0) (rhoSL C (ds.map rd0) ((pairZ C K (z0 ds)).strip τ))) &&
          symbolsCarryTheirPositions a (ds.map rd0) xs
            (drawnSL C (ds.map rd0) (rhoSL C (ds.map rd0) ((pairZ C K (z0 ds)).strip τ))) y &&
          dec x (viewX C (ds.map rd0) a xs y ((pairZ C K (z0 ds)).strip τ))))
  rw [pass_pairZ C K (z0 ds) τ, pass_zero C (z0 ds), drawn_strip C K (z0 ds) τ,
    viewX_strip C K a xs (z0 ds) y τ, carriesX_z0 a xs (z0 ds)]
  simp only [Bool.true_and, Bool.and_assoc]

/-- **The link is the link without proof of work, with the bits added.** -/
def linkPair : ProtoPair (linkProtocolOfRoundData C (ds.map rd0) a xs dec) (linkProtocolOfRoundData C ds a xs dec) :=
  ⟨pairL C K ds, link_accept C K ds a xs dec⟩

/-- **The link, round-by-round soundness, both ways.** -/
theorem link_sound_iff (L : X → (twoExternalStrings (2 ^ a) SgX).Str → Prop)
    (ε : Err (_root_.Run.Twin.up (SOf C (ds.map rd0)))) :
    (linkProtocolOfRoundData C (ds.map rd0) a xs dec).Sound L ε ↔
      (linkProtocolOfRoundData C ds a xs dec).Sound L ((pairL C K ds).down ε) :=
  (linkPair C K ds a xs dec).sound_iff L ε

include K in
/-- The link without proof of work accepts some transcript at (x, y) if and only if the link
does. -/
theorem link_accepts_iff (x : X) (y : (twoExternalStrings (2 ^ a) SgX).Str) :
    (∃ τ, (linkProtocolOfRoundData C (ds.map rd0) a xs dec).accept x y τ = true) ↔
      ∃ τ', (linkProtocolOfRoundData C ds a xs dec).accept x y τ' = true :=
  (linkPair C K ds a xs dec).accepts_iff x y

end

/-! ## 3. With the link's annotation -/

/-- The chain's pair, fitting "local rounds only". -/
def bpairZ : {l₀ l : List RD} → (z : Z0 l₀ l) →
    BPair (_root_.Run.Twin.allLo (SL C l₀)) (_root_.Run.Twin.allLo (SL C l))
  | _, _, .nil => ()
  | _, _, .cons d z => ((rpZ C K d).slot .lo, bpairZ z)

theorem toPair_bpairZ : ∀ {l₀ l : List RD} (z : Z0 l₀ l), (bpairZ C K z).toPair = pairZ C K z
  | _, _, .nil => rfl
  | _, _, .cons d z => congrArg (fun v => (rpZ C K d, v)) (toPair_bpairZ z)

section
variable (ds : List RD) (a : ℕ) (xs : List XO) {X : Type} (dec : X → View → Bool)

/-- The link's pair, fitting its annotation. -/
def bpairL :
    BPair (_root_.Run.Twin.allLo (SOf C (ds.map rd0))) (_root_.Run.Twin.allLo (SOf C ds)) :=
  BPair.consSlot (s0 C).up (bpairZ C K (z0 ds))

theorem toPair_bpairL : (bpairL C K ds).toPair = pairL C K ds :=
  (toPair_consSlot (s0 C).up (bpairZ C K (z0 ds))).trans
    (congrArg (Pair.cons (s0 C).up) (toPair_bpairZ C K (z0 ds)))

/-- The link with its annotation. -/
def linkBatchPair : BatchPair
    ⟨linkProtocolOfRoundData C (ds.map rd0) a xs dec, _root_.Run.Twin.allLo (SOf C (ds.map rd0))⟩
    ⟨linkProtocolOfRoundData C ds a xs dec, _root_.Run.Twin.allLo (SOf C ds)⟩ :=
  ⟨bpairL C K ds, fun x y τ =>
    (link_accept C K ds a xs dec x y τ).trans
      (congrArg (fun p : Pair (_root_.Run.Twin.up (SOf C (ds.map rd0)))
            (_root_.Run.Twin.up (SOf C ds)) =>
          (p.passTr τ && (linkProtocolOfRoundData C (ds.map rd0) a xs dec).accept x y (p.strip τ)))
        (toPair_bpairL C K ds).symm)⟩

theorem linkBatchPair_toPair : (linkBatchPair C K ds a xs dec).pair.toPair = pairL C K ds :=
  toPair_bpairL C K ds

end

end AtPublicFiles.Climb

#print axioms AtPublicFiles.Climb.link_accept
#print axioms AtPublicFiles.Climb.link_sound_iff
#print axioms AtPublicFiles.Climb.link_accepts_iff
#print axioms AtPublicFiles.Climb.linkBatchPair
#print axioms AtPublicFiles.Climb.pairL_bits
