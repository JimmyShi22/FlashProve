-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdSwitch.lean: the zero-knowledge code switch "with lists" as an interactive oracle reduction.

In standard terms: the reduction turns the claim "the input word is an encoding under Cin (for
knowledge soundness: lies within e long positions of one) whose message meets one linear equation"
into the same kind of claim on a new word under Cout (within e'). "With lists": e and e' are any
radii; in place of unique decoding, the statements on knowledge soundness take a bound L on the list
of Cout at e' (`D.Cout.ListAt e' L`).

Definitions and statements (each a `Prop` in `Cb.Spec`). The proofs are in
Cb/Ld/LdSwitchProofs.lean, but for `Spec.ldSwitch_blind_of_sim` and `Spec.ldSwitch_blind_of_private`
(Cb/Ld/LdSwitchPrivProofs.lean) and `Spec.ldSwitch_goodT` (Cb/Ld/LdSwitchTop.lean). The mathematics
on plain vectors is in Cb/Ld/LdSwitchWords.lean; the joints are those of Cb/Ld/LdRel.lean.
The reduction is `ldSwitch D`, an `IOR` (Ior/Ior.lean), for data `D : LdSw E P P' St`; the codes are
of type `LdCode` (Cb/Ld/LdRel.lean). The set P of the input's long positions is not empty
(`[Nonempty P]`) wherever `ldSwitch D` is spoken of: the second round's definition needs it.

From: the main relation of a code Cin read under its transformation, with a linear form sl:
statement (target, state; native word, read at long positions), witness (message, randomness).
To: the main relation of another code Cout read under its transformation, with the linear form sl'
that is defined here.
The new message is (old message, old encoding randomness, a fresh pad): the old randomness becomes a
part of the message, so that the old codeword is a linear function of the new message; the pad is
there for the sample alone.
Two rounds, none merged.
  Round 1: the prover sends a native word of Cout as oracles (honest: the encoding of the new
  message; pad and new encoding randomness uniform and independent). The verifier sends a seed ρo of
  the sample map Zo.
  Round 2: the prover sends, in the clear, one answer for each row of the sample (honest: the rows
  of Zo at ρo, applied to the new message). The verifier sends t long positions of the input and a
  seed ρb of the zero-evader Zb, in one message.
  Then the verifier reads the input at the t long positions, reads nothing of the new word, never
  rejects, and outputs
    target': the combination, with the coefficients of ρb, of the old target, the answers, and all
    coordinates of the long symbols read;
    state': for each of these rows its own state (`rowSt`), and ρb.
  sl' is the combination of the rows as forms on the new message: sl, 0 on old randomness and pad;
  the rows of the sample; the rows of the generator of Cin under its transformation, 0 on the pad.
  The new implicit instance is the word sent, read under the transformation of Cout: a query to it
  costs the native queries that this transformation makes.
The extractor (`back`) goes backwards and reads the witness of the output statement alone. No
decoding, no oracle, no verifier message.
The relaxations are existential (`ConL`, Cb/Ld/LdRel.lean): the witness's encoding is within e long
positions (input), e' long positions (output).
The errors are counts of values of one verifier message; L bounds the list of Cout under its
transformation at e' (pairs (message, randomness) within e' of a native word). `Zo.OK`
(Cb/Gen/OodDec.lean) says that a non-zero vector has all answers 0 at no more than Zo.err seeds;
`Zb.OK` (Cb/Gen/BatEvader.lean), that the coefficients of at most Zb.err seeds annihilate a non-zero
vector.
  Round 1: (L choose 2) · Zo.err; as a probability at most L²/2 · (error of the sample).
  Round 2: (|P| - e - 1)^t · |seeds of Zb| + |P|^t · (L · Zb.err);
    as a probability ((|P| - e - 1)/|P|)^t + L · (error of the zero-evader).
The bad values (`ldSwBad`) are those of Cb/Ld/LdSwitchWords.lean, for the list `Lst`.

Honest-verifier zero knowledge, in our exact form with further reads (Ior/Honest.lean), from
two hypotheses:
  `Zo.Blind good`: at every good seed the law of the answers, over a uniform pad, does not depend on
    old message and randomness. The notion with a simulator at error 0 (Cb/Gen/OodDecPad.lean:
    `PrivateSim`) gives it at all seeds (`Spec.ldSwitch_blind_of_sim`); uniform answers at the good
    seeds (`Private`) give it too (`Spec.ldSwitch_blind_of_private`).
  `Cout.Zk t'`: the native symbols of an encoding that are read for any t' long positions have a law
    that does not depend on the message.
  The budget of the block: the further positions are native positions read for at most t' long
  positions of the new word. The simulator (`ldSwSim`) runs the honest prover on the message 0 and
  the randomness 0. It is given the input's long symbols at the verifier's t positions (the
  positions are uniform) and nothing else of the input (by type); it does not use them: they enter
  the new target, not the view (exactly: `IOR.Honest.ExactWith`, `IOR.given`, Ior/Honest.lean:
  `∀ x y w, Ri x y w → ∀ ρ, ρ ∉ H.Hid w x → ∀ T, bud ρ T →`
  `H.output w x ρ T = S x ρ T (Ei.ans (R.given ρ T) y)`).
  Our own variant, not the text's: the parameter "good". The seeds that are not good are a public
  bad set of the honest side (the prover gives notice there). The text has no such seeds: its prover
  always answers. With good = all seeds nothing is withheld, and that case (`Spec.ldSwitch_goodT`)
  is the rendering of the text's block, with both its zero-knowledge errors 0.

Main names:
  `Spec.ldSwitch_data`: two rounds; nothing is tied; the verifier reads nothing of the new word and
    at most t long positions of the input; a new long position has no source in the input and the
    declared native sources in the word sent (at most b if the transformation of Cout is b-local);
    what is withheld.
  `Spec.ldSwitch_acc`: under `D.Cin.Laws`, completeness; for good = all seeds it is perfect (nothing
    is withheld).
  `Spec.ldSwitch_know`, `Spec.ldSwitch_literal`: under the hypotheses of their statements,
    round-by-round knowledge soundness in the working form (`Know`, Ior/Know.lean) and in the form
    with a knowledge state function (`HasRbrKnowledgeWith`, Ior/KnowCollLit.lean), same errors.
  `Spec.ldSwitch_exactWith`: see its statement.
  `Spec.ldSwitch_good`: under the hypotheses of its statement, the bundle `IOR.Good`
    (Ior/Chain.lean), any core.
  `Spec.ldSwitch_goodT`: under the hypotheses of its statement, the bundle `IOR.GoodT` with the core
    `Unit`, from privacy of the sample with a simulator at error 0; nothing withheld, in this sense:
    `pBad` = 0 (`IOR.Nums`, Ior/Chain.lean).

Limits: the statements ask of Cin the laws (used: encoder and transformation are linear), and of
Cout that its transformation reads what it declares (`Reads`), the list bound, and `Zk`.
Neither linearity of the encoder or of the transformation of Cout nor injectivity of an encoder is
used. The text asks for an injective linear encoder of the new code: here less is asked; injectivity
is what makes L the number of codewords.
DECLARED DIFFERENCES to the paper that this protocol builds on (lean/CREDITS.md), beside those of
Cb/Ld/LdRel.lean and Cb/Ld/LdSwitchWords.lean.
(1) Zero knowledge is exact (both hypotheses at error 0, or with a public set of bad seeds) where
    the text has two statistical errors that add, and is against every set of further positions
    within the budget where the text has uniform positions. (Zero knowledge here:
    `IOR.Honest.ExactWith`, Ior/Honest.lean.)
(2) The witness of a relaxation does not hold the corrected word, so the extractor does not encode
    anew.
(3) A state of sl' gives each row a state of its own, as in the text; states that no verifier
    outputs (different seeds in different rows) are allowed and harmless.
(4) The last verifier message is analysed in two substeps in Cb/Ld/LdSwitchWords.lean (`Bad2a`,
    `Bad2b`); the state between them is not a state of a transcript and is not named here.
This file says nothing on the sizes of L and of the two maps' errors: a bound that exceeds the
number of values says nothing; for t = 0 the second error is everything.
It says nothing on running times or on succinctness of forms.
How a protocol uses the block is not this file's matter.
The protocol restates, in our own words, a construction of that text (lean/CREDITS.md).

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdRelKit
import Cb.Ld.LdSwitchWords
import Cb.Gen.OodDecPad
import Ior.KnowCollGood
import Ior.KnowCollLit
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood

/-! ## Tools that are not about the switch -/

/-- The transformation reads what it declares. -/
def LdCode.Reads {E P : Type} (C : LdCode E P) : Prop :=
  ∀ (f g : C.Word) x, (∀ p ∈ C.src x, f p = g p) → C.T f x = C.T g x

/-- At every good seed the law of the answers, over a uniform pad, does not depend on the entries
proper. -/
def Ood.Sample.Blind {E J₀ Qo : Type} [Field E] [Fintype E] [Fintype J₀] [Fintype Qo]
    [DecidableEq Qo] (Z : Sample E (J₀ ⊕ Qo)) (good : Z.D → Prop) : Prop :=
  ∀ ρ, good ρ →
    ∀ v v' : J₀ → E, (unif (Qo → E)).map (fun ro => Z.val ρ (ldNew v ro)) =
      (unif (Qo → E)).map fun ro => Z.val ρ (ldNew v' ro)

/-! ## The data -/

/-- The data of a code switch. P, P': the long positions of the two codes; St: the states of the old
form. -/
structure LdSw (E P P' St : Type) where
  Cin   : LdCode E P
  [finAa : Fintype Cin.Aa]
  Cout  : LdCode E P'
  /-- the coordinates of the pad -/
  Qo    : Type
  [finQo : Fintype Qo]
  [decQo : DecidableEq Qo]
  /-- how the coordinates of a message of Cout are named: old message, old randomness, pad -/
  place : (Cin.J ⊕ Cin.Q) ⊕ Qo ≃ Cout.J
  /-- the old form -/
  sl    : Slf E St Cin.J
  /-- the sample on new messages -/
  Zo    : Sample E ((Cin.J ⊕ Cin.Q) ⊕ Qo)
  /-- the number of long positions of the input that the verifier reads -/
  t     : ℕ
  /-- the coefficients of the batching -/
  Zb    : Evader E (LdRow Zo.S t Cin.Aa)

attribute [instance] LdSw.finAa LdSw.finQo LdSw.decQo

namespace LdSw
variable {E P P' St : Type} (D : LdSw E P P' St)

/-- the coordinates of an old full message, and of a new message -/
abbrev K : Type := D.Cin.J ⊕ D.Cin.Q
abbrev Nw : Type := D.K ⊕ D.Qo

/-- A message of Cout by its named coordinates, and back. -/
def un (m' : D.Cout.J → E) : D.Nw → E := fun n => m' (D.place n)
def re (u : D.Nw → E) : D.Cout.J → E := fun j => u (D.place.symm j)

/-- The new message. -/
def msg (w : (D.Cin.J → E) × (D.Cin.Q → E)) (ro : D.Qo → E) : D.Nw → E :=
  ldNew (Sum.elim w.1 w.2) ro

/-- The extractor: old message and old randomness, cut out of the new message. -/
def back (w' : (D.Cout.J → E) × (D.Cout.Q → E)) : (D.Cin.J → E) × (D.Cin.Q → E) :=
  (fun j => D.un w'.1 (.inl (.inl j)), fun q => D.un w'.1 (.inl (.inr q)))

/-- The state of a row: the old state; a seed of the sample; a long position and a coordinate. -/
def rowSt : LdRow D.Zo.S D.t D.Cin.Aa → Type
  | .inl _ => St
  | .inr (.inl _) => D.Zo.D
  | .inr (.inr _) => P × D.Cin.Aa

/-- The states that the verifier gives to the rows. -/
def stOf (z : St) (ρo : D.Zo.D) (Qs : Fin D.t → P) : ∀ b, D.rowSt b
  | .inl _ => z
  | .inr (.inl _) => ρo
  | .inr (.inr ic) => (Qs ic.1, ic.2)

/-- the states of the new form -/
abbrev St' : Type := (∀ b, D.rowSt b) × D.Zb.D

variable [Field E]

/-- the data on vectors -/
@[reducible] def W : LdSwW E D.K D.Qo P D.Cin.Aa := ⟨D.Cin.row, D.Zo, D.t, D.Zb⟩

/-- The rows, as linear forms with a state on the named coordinates of a new message. -/
def rowSl : ∀ b, Slf E (D.rowSt b) D.Nw
  | .inl _ => (D.sl.padR (J' := D.Cin.Q)).padR (J' := D.Qo)
  | .inr (.inl s) => fun ρ => D.Zo.mat ρ s
  | .inr (.inr _) => D.Cin.rowSlf.padR (J' := D.Qo)

/-- The new form: the rows, batched into one. -/
def sl' : Slf E D.St' D.Cout.J := fun x j => Slf.bat D.Zb.ze D.rowSl x (D.place.symm j)

/-- The list of the word g: the new messages that are represented within e' long positions of g. -/
def Lst [Finite P'] (e' : ℕ) (g : D.Cout.Word) (u : D.Nw → E) : Prop :=
  ∃ r', D.Cout.Near e' g (D.Cout.enc (D.re u) r')

variable [Fintype P] [Nonempty P]

/-- the two rounds -/
abbrev sh : Shape :=
  [D.Cout.sendRound Unit D.Zo.D (), plainRound (D.Zo.S → E) ((Fin D.t → P) × D.Zb.D) fun _ => 0]

def pt : D.sh.IsPoint := (D.Cout.sendPoint _ _ _, plainPoint _ _ _, ())

end LdSw

section
variable {E P P' St : Type} [Field E] [Fintype P] [Nonempty P] (D : LdSw E P P' St)

open Classical in
/-- The code switch. -/
def ldSwitch : IOR (E × St) D.Cin.ext (E × D.St') D.Cout.ext where
  shape := D.sh
  blinded _ := true
  extReads ρ := Finset.univ.image ρ.2.1.1
  reads _ := ∅
  out x y τ :=
    some (D.W.tgt' x.1 τ.2.2.1.2 (D.Cin.T y) τ.2.2.2.1, (D.stOf x.2 τ.2.1 τ.2.2.2.1.1, τ.2.2.2.1.2))
  imp _ τ := τ.1.1
  srcE _ _ := ∅
  srcO _ q := (D.Cout.src q).image Sum.inl
  tie _ _ := ∅

/-- A set of positions of the prover's oracles, as a set of native positions of the new word. -/
def ldSwSet (T : Finset (OPos D.sh)) : Finset D.Cout.nat.Pos :=
  Finset.toLeft (α := D.Cout.NP) (β := Empty ⊕ Empty) T

variable [Fintype E]

/-- The honest side. Coins: the pad, the new encoding randomness. At the seeds that are not good the
prover gives notice. -/
def ldSwitchHon (good : D.Zo.D → Prop) :
    (ldSwitch D).Honest D.Cin.N.Wit D.Cout.N.Wit where
  Coin := (D.Qo → E) × (D.Cout.Q → E)
  strat w x c := ((D.Cout.enc (D.re (D.msg w c.1)) c.2, ()),
    fun ρo =>
      (((), D.Zo.val ρo (D.msg w c.1)),
        fun ch =>
          ((D.W.tgt' x.1 (D.Zo.val ρo (D.msg w c.1)) (D.Cin.T (D.Cin.enc w.1 w.2)) ch,
              (D.stOf x.2 ρo ch.1, ch.2)),
            (D.re (D.msg w c.1), c.2))))
  Bad := {ρ | ¬ good ρ.1}
  Hid _ _ := ∅

open Classical in
/-- The simulator: notice at a seed that is not good; else the honest prover on the message 0 and
the randomness 0. It uses nothing of what it is given but ρ and T. -/
def ldSwSim (good : D.Zo.D → Prop) : IOR.Honest.Sim (ldSwitch D) := fun x ρ T _ =>
  if good ρ.1 then
    (unif ((D.Qo → E) × (D.Cout.Q → E))).map fun c =>
      some ((ldSwitch D).view T (((ldSwitchHon D good).strat (0, 0) x c).run ρ).1)
      else PMF.pure none

variable [Fintype P']

/-- The bad values for the statement a. -/
def ldSwBad (e e' : ℕ) (a : (E × St) × D.Cin.Word) : BadFam D.sh :=
  (fun m => {ρo | D.W.Bad1 (D.Lst e' m.1) ρo},
    fun m ρo =>
      (fun m₂ => {c | D.W.Bad2 (D.Lst e' m.1) e (ldPad (D.sl a.1.2)) a.1.1 (D.Cin.T a.2) ρo m₂.2 c},
        fun _ _ => ()))

/-- The numbers. -/
def ldSwNums (Kc : Type) (good : D.Zo.D → Prop) (e L t' : ℕ) :
    IOR.Nums Kc (ldSwitch D) :=
  ⟨(D.W.err1 L, (D.W.err2 e L, ())), prRho {ρ : Rho D.sh | ¬ good ρ.1}, 0,
    fun _ T => D.Cout.budT t' (ldSwSet D T), fun _ => ∅⟩

/-- The knowledge state witnesses. -/
abbrev LdSw.KW : Type := D.Cin.N.Wit ⊕ D.Cout.N.Wit

open Classical in
/-- The knowledge state function. -/
def ldSwState (e e' : ℕ) (a : (E × St) × D.Cin.Word) : PTr D.sh → D.KW → Bool
  | .atP (.inl _), s => decide (onLeft (ConL D.Cin.N e D.sl.Holds) a s)
  | .atV (.inl _), s => decide (onLeft (ConL D.Cin.N e D.sl.Holds) a s)
  | .atP (.inr (m, ρo, _)), s => decide (onLeft (ConL D.Cin.N e D.sl.Holds) a s ∨ D.W.Bad1 (D.Lst e' m.1) ρo)
  | .atV (.inr (m, ρo, _)), s => decide (onLeft (ConL D.Cin.N e D.sl.Holds) a s ∨ D.W.Bad1 (D.Lst e' m.1) ρo)
  | .full τ, s => decide (∃ b, (ldSwitch D).red.out a τ = some b ∧ onRight (ConL D.Cout.N e' D.sl'.Holds) b s)

end

namespace Spec
open IOR

open Classical in
/-- The data of the code switch. -/
def ldSwitch_data : Prop :=
  ∀ (E P P' St : Type) [Field E] [Fintype E] [Fintype P] [Nonempty P] (D : LdSw E P P' St),
    (ldSwitch D).shape.length = 2 ∧
    (ldSwitch D).ImpBy (fun _ o p => o (Sum.inl p)) ∧
    (∀ ρ p, (ldSwitch D).tie ρ p = ∅) ∧
    (∀ ρ, (ldSwitch D).reads ρ = ∅) ∧
    (∀ ρ, ((ldSwitch D).extReads ρ).card ≤ D.t) ∧
    (∀ ρ q, (ldSwitch D).srcE ρ q = ∅) ∧
    (∀ ρ q p, p ∈ (ldSwitch D).srcO ρ q ↔ ∃ n ∈ D.Cout.src q, Sum.inl n = p) ∧
    (∀ b, D.Cout.LocalLE b → ∀ ρ q, ((ldSwitch D).srcO ρ q).card ≤ b) ∧
    ∀ good, (ldSwitchHon D good).Bad = {ρ | ¬ good ρ.1} ∧ ∀ w x, (ldSwitchHon D good).Hid w x = ∅

/-- The new form at the verifier's state is the batched form on vectors, at the old form padded by 0
on the old randomness. -/
def ldSwitch_form : Prop :=
  ∀ (E P P' St : Type) [Field E] (D : LdSw E P P' St) (z : St) (ρo : D.Zo.D)
      (c : D.W.Ch2) (n : D.Nw),
    D.sl' (D.stOf z ρo c.1, c.2) (D.place n) = D.W.form' (ldPad (D.sl z)) ρo c n

/-- Completeness. Under `D.Cin.Laws`, P not empty: with good = all seeds nothing is withheld:
perfect completeness. -/
def ldSwitch_acc : Prop :=
  ∀ (E P P' St : Type) [Field E] [Fintype E] [Fintype P] [Nonempty P]
      (D : LdSw E P P' St) (good : D.Zo.D → Prop),
    D.Cin.Laws → (ldSwitchHon D good).Acc (Con D.Cin.N D.sl.Holds) (Con D.Cout.N D.sl'.Holds)

/-- Under the hypotheses below, the bad sets are within the errors. -/
def ldSwitch_within : Prop :=
  ∀ (E P P' St : Type) [Field E] [Fintype E] [Fintype P] [Nonempty P] [Fintype P']
      (D : LdSw E P P' St) (e e' L : ℕ),
    D.Cout.ListAt e' L → D.Zo.OK → D.Zb.OK →
    ∀ a, (ldSwBad D e e' a).Within (D.W.err1 L, (D.W.err2 e L, ()))

/-- The backward step, under `D.Cin.Laws`, P not empty: no bad value; then the extractor turns a
witness of the output statement in the relaxation into one of the input statement. -/
def ldSwitch_clean : Prop :=
  ∀ (E P P' St : Type) [Field E] [Fintype E] [Fintype P] [Nonempty P] [Fintype P']
      (D : LdSw E P P' St) (e e' : ℕ),
    D.Cin.Laws →
    ∀ a (τ : Tr D.sh) b w', (ldSwBad D e e' a).Clean τ → (ldSwitch D).red.out a τ = some b →
      ConL D.Cout.N e' D.sl'.Holds b w' → ConL D.Cin.N e D.sl.Holds a (D.back w')

/-- Round-by-round knowledge soundness, working form: any radii. -/
def ldSwitch_know : Prop :=
  ∀ (E P P' St : Type) [Field E] [Fintype E] [Fintype P] [Nonempty P] [Fintype P']
      (D : LdSw E P P' St) (e e' L : ℕ),
    D.Cin.Laws → D.Cout.ListAt e' L → D.Zo.OK → D.Zb.OK →
    (ldSwitch D).red.Know (fun _ => True) (ConL D.Cin.N e D.sl.Holds) (ConL D.Cout.N e' D.sl'.Holds)
      (fun _ _ w' => D.back w') (D.W.err1 L, (D.W.err2 e L, ()))

/-- Round-by-round knowledge soundness in the form with a knowledge state function, with the state
function "the state before, or a collision"; the round extractors: the identity, then `back`. -/
def ldSwitch_literal : Prop :=
  ∀ (E P P' St : Type) [Field E] [Fintype E] [Fintype P] [Nonempty P] [Fintype P']
      (D : LdSw E P P' St) (e e' L : ℕ),
    D.Cin.Laws → D.Cout.ListAt e' L → D.Zo.OK → D.Zb.OK →
    (ldSwitch D).red.HasRbrKnowledgeWith (fun _ => True) (onLeft (ConL D.Cin.N e D.sl.Holds))
      (onRight (ConL D.Cout.N e' D.sl'.Holds)) (ldSwState D e e')
      (fun _ => RExt.ofFull D.sh fun _ w' => D.back w') (D.W.err1 L, (D.W.err2 e L, ()))

/-- Privacy with a simulator, error 0, gives blindness at all seeds. -/
def ldSwitch_blind_of_sim : Prop :=
  ∀ (E J₀ Qo : Type) [Field E] [Fintype E] [Fintype J₀] [Fintype Qo]
      [DecidableEq Qo] (Z : Sample E (J₀ ⊕ Qo)),
    Z.PrivateSim E → Z.Blind fun _ => True

/-- Uniform answers at the good seeds give blindness there. -/
def ldSwitch_blind_of_private : Prop :=
  ∀ (E J₀ Qo : Type) [Field E] [Fintype E] [Fintype J₀] [Fintype Qo] [DecidableEq Qo]
      (Z : Sample E (J₀ ⊕ Qo)) (good : Z.D → Prop),
    Z.Private E good → Z.Blind good

/-- Under `D.Zo.Blind good` and `D.Cout.Zk t'`, P not empty: honest-verifier exact zero knowledge,
with the simulator named, for every input relation, in this sense:
`(ldSwitchHon D good).ExactWith Ri (fun _ T => D.Cout.budT t' (ldSwSet D T)) (ldSwSim D good)`
(`IOR.Honest.ExactWith`, Ior/Honest.lean; the budget: the head). -/
def ldSwitch_exactWith : Prop :=
  ∀ (E P P' St : Type) [Field E] [Fintype E] [Fintype P] [Nonempty P] (D : LdSw E P P' St)
      (good : D.Zo.D → Prop) (t' : ℕ) (Ri : E × St → D.Cin.ext.Str → D.Cin.N.Wit → Prop),
    D.Zo.Blind good → D.Cout.Zk t' →
    (ldSwitchHon D good).ExactWith Ri (fun _ T => D.Cout.budT t' (ldSwSet D T)) (ldSwSim D good)

/-- Under the hypotheses below, the code switch leads from the main relation of Cin to the main
relation of Cout. -/
def ldSwitch_good : Prop :=
  ∀ (E P P' St : Type) [Field E] [Fintype E] [Fintype P] [Nonempty P] [Fintype P']
      (D : LdSw E P P' St) (Kc : Type) (core : D.Cin.N.Wit → Kc)
      (good : D.Zo.D → Prop) (e e' L t' : ℕ),
    D.Cin.Laws → D.Cout.Reads → D.Cout.ListAt e' L → D.Zo.OK → D.Zb.OK →
    D.Zo.Blind good → D.Cout.Zk t' →
    Good (ldSwitch D) (ldSwitchHon D good) (D.Cin.rels D.sl e core)
      (D.Cout.rels D.sl' e' fun w' => core (D.back w'))
      (fun _ _ w' => D.back w') (ldSwNums D Kc good e L t')

/-- Under the hypotheses below, the same with `GoodT` and the core `Unit`, from privacy of the
sample with a simulator at error 0; nothing is withheld, in this sense: `pBad` = 0. -/
def ldSwitch_goodT : Prop :=
  ∀ (E P P' St : Type) [Field E] [Fintype E] [Fintype P] [Nonempty P] [Fintype P']
      (D : LdSw E P P' St) (e e' L t' : ℕ),
    D.Cin.Laws → D.Cout.Reads → D.Cout.ListAt e' L → D.Zo.OK → D.Zb.OK →
    D.Zo.PrivateSim E → D.Cout.Zk t' →
    GoodT (ldSwitch D) (ldSwitchHon D fun _ => True) (D.Cin.rels D.sl e fun _ => ())
      (D.Cout.rels D.sl' e' fun _ => ()) (fun _ _ w' => D.back w')
      (ldSwNums D Unit (fun _ => True) e L t') ∧
    (ldSwNums D Unit (fun _ => True) e L t').pBad = 0

end Spec
end Cb
