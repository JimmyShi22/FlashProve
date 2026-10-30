-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/M1/Law.lean: M1's protocol-free statements. Definitions, and each theorem-to-be as a `def … : Prop`. No proof.
The plain lines, who pays what, and the prover's duties: the head of Johnson/M1/Statement.lean.

  Ledger, Ledger.free, Ledger.Pays, Spec.ledgerLaw    blocks of shown values in one order; the bare law
  PrivateStop, Ledgered, OneLawOff, Spec.chain        a view as a public function of a ledger's tuple; one law, challenge by
                                                      challenge, off the private stop
  realLaw, simLaw, Spec.chainStat, StopBound          what may be said: statistical
  THE BLOCKS THAT PAY, in the model: each says «at FIXED data and earlier coins, uniform over the block's own coins»:
  Spec.shiftPays      a bijection of the coins, shifted: a fold's 2 k + 1, a masked sumcheck's elements, a split's share,
                      the last step's open words
  Spec.tailPays       the opened columns of a message without a sample (a fresh mask), over its tails
  Spec.messagePays    one sampled oracle message: (its answers, its opened columns) over (its pads, its tails)
  Spec.base, Spec.baseRows   the last step: one code; rows under several codes, each read at its own points

What is not claimed. That any protocol has a ledger, or that any prover's message has one of these forms.
-/
import Code.FreshWide
import Johnson.LinkSim.Tail
import Johnson.SendSim.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace OnBytes.M1

open Code (WideLaw)
open OnBytes.LinkSim (sym)
open OnBytes.SendSim (tl)
open scoped ENNReal

/-! ## (B) The chain -/

/-- A ledger of n blocks of shown values over data D. Block i has coins C i of its own; what it shows may hang, in any way,
on the data and on the coins of blocks in front of it. -/
structure Ledger (D : Type) (n : Nat) where
  C : Fin n → Type
  Y : Fin n → Type
  [fC : ∀ i, Fintype (C i)]
  [nC : ∀ i, Nonempty (C i)]
  [fY : ∀ i, Fintype (Y i)]
  [nY : ∀ i, Nonempty (Y i)]
  show_ : (i : Fin n) → D → ((j : Fin n) → j < i → C j) → C i → Y i

attribute [instance] Ledger.fC Ledger.nC Ledger.fY Ledger.nY

/-- All that is shown, at data d and coins c. -/
def Ledger.free {D : Type} {n : Nat} (L : Ledger D n) (d : D) (c : (i : Fin n) → L.C i) :
    (i : Fin n) → L.Y i :=
  fun i => L.show_ i d (fun j _ => c j) (c i)

/-- Every block pays: at every fixed data and earlier coins, its own uniform coins make what it shows uniform. -/
def Ledger.Pays {D : Type} {n : Nat} (L : Ledger D n) : Prop :=
  ∀ i d pre, WideLaw (L.show_ i d pre)

/-- (B0) THE BARE LAW: if every block pays, the whole tuple is uniform, at every data. A block may be nonlinear (the
sumcheck's round in Y is). Widens Code.tri_law from three blocks to n. -/
def Spec.ledgerLaw : Prop :=
  ∀ (D : Type) (n : Nat) (L : Ledger D n), L.Pays → ∀ d, WideLaw (L.free d)

/-- The private stop: at ds no public stop has fired, and the prover stops for a reason that hangs on the witness. bad: the
public bad set, of challenges alone. hid: the rest of the withheld set; it may read the witness. NEITHER READS A COIN: so it is
in the frame: Part.bad takes challenges alone, Part.hid what the part sees of the input and challenges
(Johnson/Desc/ProofFile/Honest/Frame.lean:676, :682), and silentAt takes the input and the draws (Honest/Rule.lean:82). -/
def PrivateStop {Wit Chal : Type} (bad : Chal → Prop) (hid : Wit → Chal → Prop) : Wit → Chal → Prop :=
  fun w ds => ¬ bad ds ∧ hid w ds

/-- A prover's view is Ledgered if, at every list of challenges ds, it is a PUBLIC function of a ledger's tuple at every
witness at which `stop` does not hold at ds. The ledger may hang on ds, not on the witness. At a ds in the public bad set the
view is the notice: n = 0. viewOf, stop, pubOf, Coin: letters. -/
def Ledgered {Wit Pub Chal View : Type} (pubOf : Wit → Pub) (Coin : Type) [Fintype Coin]
    [Nonempty Coin] (viewOf : Wit → Chal → Coin → View) (stop : Wit → Chal → Prop) : Prop :=
  ∀ ds : Chal, ∃ (n : Nat) (L : Ledger Wit n) (e : Coin ≃ ((i : Fin n) → L.C i))
    (made : Pub → ((i : Fin n) → L.Y i) → View),
    L.Pays ∧ ∀ w, ¬ stop w ds → ∀ c, viewOf w ds c = made (pubOf w) (L.free w (e c))

/-- CHALLENGE BY CHALLENGE: at every ds outside Stop(w), the view's law is simAt's, which is handed the public result and ds.
So two witnesses with one public result have one law at every ds outside Stop(w) ∪ Stop(w'). Nothing is said at a ds inside,
and NOTHING OF A LAW CONDITIONED ON NO STOP. -/
def OneLawOff {Wit Pub Chal View : Type} (pubOf : Wit → Pub) (Coin : Type) [Fintype Coin]
    [Nonempty Coin] (viewOf : Wit → Chal → Coin → View) (stop : Wit → Chal → Prop)
    (simAt : Pub → Chal → PMF View) : Prop :=
  ∀ ds w, ¬ stop w ds → (Prob.unif Coin).map (viewOf w ds) = simAt (pubOf w) ds

/-- (B) THE CHAIN. -/
def Spec.chain : Prop :=
  ∀ (Wit Pub Chal View Coin : Type) [Fintype Coin] [Nonempty Coin] (pubOf : Wit → Pub)
    (viewOf : Wit → Chal → Coin → View) (stop : Wit → Chal → Prop),
    Ledgered pubOf Coin viewOf stop → ∃ simAt, OneLawOff pubOf Coin viewOf stop simAt

/-- The honest verifier's challenges with the view. chal: the honest verifier's law: independent of the coins; uniform, but
on the elements other than 0 at a seed's factor and at a sumcheck's Y. -/
def realLaw {Wit Chal View : Type} (Coin : Type) [Fintype Coin] [Nonempty Coin] (chal : PMF Chal)
    (viewOf : Wit → Chal → Coin → View) (w : Wit) : PMF (Chal × View) :=
  chal.bind fun ds => (Prob.unif Coin).map fun c => (ds, viewOf w ds c)

/-- The same with the simulator's view. -/
def simLaw {Pub Chal View : Type} (chal : PMF Chal) (simAt : Pub → Chal → PMF View) (p : Pub) :
    PMF (Chal × View) :=
  chal.bind fun ds => (simAt p ds).map fun v => (ds, v)

/-- (B') WHAT MAY BE SAID: STATISTICAL, with the distance at most the chance of `stop`: at `PrivateStop bad hid`, of the private
stop alone. -/
def Spec.chainStat : Prop :=
  ∀ (Wit Pub Chal View Coin : Type) [Fintype Coin] [Nonempty Coin] (pubOf : Wit → Pub)
    (viewOf : Wit → Chal → Coin → View) (stop : Wit → Chal → Prop) (simAt : Pub → Chal → PMF View)
    (chal : PMF Chal), OneLawOff pubOf Coin viewOf stop simAt →
    ∀ w, Prob.tv (realLaw Coin chal viewOf w) (simLaw chal simAt (pubOf w)) ≤
      Prob.pr chal {ds | stop w ds}

/-- The bound on the stop, AS A LETTER eps WITH ITS DEFINITION: at every valid witness the honest verifier's challenges fall
into Stop(w) with probability at most eps. No value of eps is stated or used here. -/
def StopBound {Wit Chal : Type} (chal : PMF Chal) (stop : Wit → Chal → Prop) (valid : Wit → Prop)
    (eps : ℝ≥0∞) : Prop :=
  ∀ w, valid w → Prob.pr chal {ds | stop w ds} ≤ eps

/-! ## The blocks that pay, in the model -/

/-- A bijection of the block's coins, shifted by anything fixed. -/
def Spec.shiftPays : Prop :=
  ∀ (C Y : Type) [Fintype C] [Nonempty C] [Fintype Y] [Nonempty Y] [AddGroup Y] (e : C ≃ Y) (c : Y),
    WideLaw fun x : C => c + e x

/-- The opened columns of rows whose messages are FIXED (data, pads, mask entries, coefficients: all earlier), over the rows'
tails: row ρ has a message of l ρ entries and a tail of r ρ, and is read at the points pts ρ, at most r ρ of them. -/
def Spec.tailPays : Prop :=
  ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (Row : Type) [Fintype Row] [DecidableEq Row]
    (l r : Row → ℕ) (pts : Row → Finset K), (∀ ρ, (pts ρ).card ≤ r ρ) → ∀ (m : Row → ℕ → K),
    WideLaw fun t : ((ρ : Row) → Fin (r ρ) → K) =>
      ((fun ρ p => sym (r ρ) (l ρ) p.1 (m ρ) (tl (t ρ))) : (ρ : Row) → pts ρ → K)

/-- ONE SAMPLED ORACLE MESSAGE AS ONE BLOCK: over (its pads, its tails), at everything else fixed: (its answers, its opened
columns) is uniform. a0: the answers' share of what is fixed. beta: the factors, none 0. m: the rows' messages, of what is
fixed AND of the pads, in any way. -/
def Spec.messagePays : Prop :=
  ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (Row : Type) [Fintype Row] [DecidableEq Row]
    (A : Type) [Fintype A] [DecidableEq A] (l r : Row → ℕ) (pts : Row → Finset K),
    (∀ ρ, (pts ρ).card ≤ r ρ) → ∀ (a0 beta : A → K), (∀ a, beta a ≠ 0) →
    ∀ (m : (A → K) → Row → ℕ → K),
    WideLaw fun x : (A → K) × ((ρ : Row) → Fin (r ρ) → K) =>
      ((fun a => a0 a + beta a * x.1 a,
        fun ρ p => sym (r ρ) (l ρ) p.1 (m x.1 ρ) (tl (x.2 ρ))) :
        (A → K) × ((ρ : Row) → pts ρ → K))

/-- (A') THE LAST STEP, in the model, under one code. Rows ρ with message M ρ and tail R ρ, and a masking word (M★, R★);
(M★, R★, R) uniform: at every lam, every M and at most r distinct points, (M★ + lam M, R★ + lam R, the rows' symbols) is
uniform. -/
def Spec.base : Prop :=
  ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (Row : Type) [Fintype Row] [DecidableEq Row]
    (l r : ℕ) (pts : Finset K), pts.card ≤ r → ∀ (lam : K) (M : Row → Fin l → K),
    WideLaw fun x : (Row → Fin l → K) × (Row → Fin r → K) × (Row → Fin r → K) =>
      ((fun ρ j => x.1 ρ j + lam * M ρ j, fun ρ j => x.2.1 ρ j + lam * x.2.2 ρ j,
        fun (p : pts) ρ => sym r l p.1 (fun j => if h : j < l then M ρ ⟨j, h⟩ else 0)
          (tl (x.2.2 ρ))) :
        (Row → Fin l → K) × (Row → Fin r → K) × (pts → Row → K))

/-- The same with rows under several codes, each read at its own points: at the protocol's numbers a main row (256 entries)
and mask rows (1024), tails of 44, the mask rows read at the positions modulo their own length. -/
def Spec.baseRows : Prop :=
  ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (Row : Type) [Fintype Row] [DecidableEq Row]
    (l r : Row → ℕ) (pts : Row → Finset K), (∀ ρ, (pts ρ).card ≤ r ρ) →
    ∀ (lam : K) (M : (ρ : Row) → Fin (l ρ) → K),
    WideLaw fun x : ((ρ : Row) → Fin (l ρ) → K) × ((ρ : Row) → Fin (r ρ) → K) ×
        ((ρ : Row) → Fin (r ρ) → K) =>
      ((fun ρ j => x.1 ρ j + lam * M ρ j, fun ρ j => x.2.1 ρ j + lam * x.2.2 ρ j,
        fun ρ p => sym (r ρ) (l ρ) p.1 (fun j => if h : j < l ρ then M ρ ⟨j, h⟩ else 0)
          (tl (x.2.2 ρ))) :
        ((ρ : Row) → Fin (l ρ) → K) × ((ρ : Row) → Fin (r ρ) → K) × ((ρ : Row) → pts ρ → K))

/-- M1's protocol-free half. -/
def Spec.law : Prop :=
  Spec.ledgerLaw ∧ Spec.chain ∧ Spec.chainStat ∧ Spec.shiftPays ∧ Spec.tailPays ∧ Spec.messagePays ∧
    Spec.base ∧ Spec.baseRows

end OnBytes.M1
