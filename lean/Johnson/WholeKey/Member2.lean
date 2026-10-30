-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/WholeKey/Member2.lean: A SECOND MEMBER: ALL PREMISES of the statement of index privacy for
the scheme with the whole key published (PremW, Johnson/WholeKey/Premises.lean) HOLD TOGETHER at a
small object all three of whose protocols have a real round, with a test and a shared round.

Definitions, statements and proofs. A toy: nothing here is about the protocol of the release. This
file states no goal of the release.

Why. Johnson/WholeKey/Member.lean meets every clause of PremW at once, but many of them for lack of
a case: no round has a test, link and session have no round, there is one copy and one session, the
run values are of the type with one member. Here these clauses have cases.

THE OBJECT is pad2 (Hiop/Seeded/Pad2.lean). THREE INDICES: two in range, and one out of range, at
which all three honest sides stop. THE RANGE ok IS A PROPER SUBSET: the two in range. (That the
guard is needed: stops_all_forces, Johnson/WholeKey/Foes2.lean.) Each of the three verifiers reads a
symbol of each encoded index that it is about. The first table's protocol has one local round, WITH
A PROVER's ORACLE, which its verifier reads. The link has one local round. A session has two rounds:
a local one and a SHARED one (the joining round).
THE LETTERS. Digests of 32 bits, one hash block an answer. Trees of depth 0: a table has one leaf.
Request trees of depth 0. The seed is the first bit of the block; the seeds are asked AT THE
SESSION's Fiat-Shamir oracle, whose first round has the test.
  A RUN WITH A TREE: the first table's run hashes one tree of one leaf, over its oracle's symbol.
  A TEST WITH A CAP: the session's first round has a test of one bit, the block's first bit; the
    nonce is the number in the round's plain part; the wire's own number of tries and the honest
    side's cap are 3 (four tries).
  TWO COPIES (M = 1), each of which serves TWO SESSIONS (s1 = 2).
  RUN VALUES are bits: a coin of the strategy, sent in the clear; the public start of a leaf's salt
    in a run is that bit. A table's leaf salt starts with one public bit. 32 free bits each.
  THE BUDGET of reads of one table is 3: the first table is read by its own protocol and by two
    links; a copy by its link and two sessions.
All seeds are good (Gs := all), so δ = 0. At the indices in range the simulators are exact and no
honest side stops, so all six errors are 0.

WHICH OF PremW's TWENTY CLAUSES HAVE A CASE HERE, by the writer's own reading.
  ext        bites: three honest sides, each with the encoded index(es) as external strings.
  runVals    bites: the run value is a coin, read back off a plain part, in all three kinds of run.
  reads      in part: the four counts are 1, each met with equality by a verifier that reads; the
             encoding hides at three indices, with an answer that hangs on index, randomness and
             seed. But the word has one position, so it hides at EVERY budget b.
  budget₀    in part: met with equality, 1 + 2 · 1 = 3; it binds nothing, since reads holds at every
             b.
  budget₁    in part: the like.
  good       bites, at the two indices of ok: each view shows something (a symbol, a run value, an
             oracle's symbol, a bit of a verifier message sent back). Error 0.
  stops      bites: the stops that hang on the private input are everything at the index out of
             range and nothing in range. Measure 0 at ok; no stop inside the range.
  seeds      IDLE: every seed is good.
  freeT      IDLE: the verifier reads the one position of the prover's oracle, whatever is sent; the
             round has no test.
  freeL      IDLE: no prover's oracle.
  freeB      IDLE: no prover's oracle.
  wires      in part: the laws of places have a case at the one tree; uniform blocks give a uniform
             verifier message at the block; the test's laws; the external strings' wires; the code
             of answers. All depths are 0.
  fmt        bites at the session: a local round, then the joining round.
  backT      IDLE: no test.
  backL      IDLE: no test.
  backB      bites: the numbers 0 to 3 are read back.
  plain      bites: the seeds' queries stand at the oracle whose first round has the test; their
             plain parts hold the nonce for 0.
  coherent   in part: each round sends one component alone.
  isLocal    bites: three verifiers that compare what they read.
  coins      in part: the enumerations, the tables' salts, len₀, the three laws of a run's coins,
             the rounds, winT and lenT have a case. okT, okL, okB are idle (every run value is of
             the right form). lenL, lenB, winL, winB are met, and no leaf of such a run is hashed.
  In all: eight bite, six in part, six are idle. A STRICTER COUNT IS POSSIBLE: six whole, eight in
  part, six idle (the same six).

WHAT THIS MEMBER DOES NOT TRY.
  All seven error letters are 0, every seed is good and every run value is of the right form: so of
    zetaW's five summands those for the simulators' errors, the stops and the seeds are 0 here.
    (Letters at which zO or hO is 1: Johnson/WholeKey/FoeZeta.lean.)
  No salt of a leaf hides anything that the pad does not hide already: what the hashes are there to
    hide has no case.
  No inner node of a tree is asked: all trees have depth 0.
  ζ + ζ < 1 holds at few requests alone. By hand, not proved here: the summand for an overrun is 0
    up to two requests, 1/4 at three, 5/8 at four, and 1 or more from five on.
  That a proof's string is ever handed out is not shown here: string_often_pad2,
    Johnson/WholeKey/FoeScheme.lean (but for probability 1/16, at one request).

Main names (namespace OnBytes.WholeKey.Member2).
  aT, aL, wT, wL, wB1, wB2, gr, W2, S2, cA2, p2, recs2, sm2, ok2, at2, cn2, nu2   the letters.
  premW_pad2   ALL PREMISES TOGETHER.
  zeta_pad2    the statement's error at these letters, at one query and THREE requests (one more
    than a copy serves, so the summand for an overrun is alive), is below 1: at most
    1/4 + 204 / 2^32.
The letters, the proofs of the wires' laws and the sum over the oracles' names follow
Johnson/WholeKey/Member.lean closely.

Limits. A toy. The summands of zetaW for the simulators' errors, the stops and the seeds are 0 here;
those for an overrun and for the hashes are alive. The word has one symbol, so the budget 3 counts
repeated reads of one position. zeta_pad2 says "below 1", which is too low a bar for hiding: that
zetaW 1 3 + zetaW 1 3 < 1: zeta_pad2_half, Johnson/WholeKey/Main.lean.
"PASSES THE BAR" IS NOT "HIDES": ζ + ζ < 1 is where the statement begins to speak: necessary, not
enough. Argued, not typed: a prover that tells its index and hands no string in a share β of its
proofs, with a simulator that mixes the two indices, would sit at (1 - β)/2 and, if β is not 0, pass
it (of the teller of Johnson/WholeKey/FoeScheme.lean Lean has β ≤ 1/16 alone: so 15/32 or more).
What shuts out a prover that tells outright is ζ + ζ + α < 1, with α the error of completeness,
which β does not exceed (the typed half: teller_not_private there: 1 ≤ ζ + ζ + 1/16). QUOTE THE
NUMBER: twice the error is at most about 0.50 here, at one query and three requests (at the first
member at most about 0.23). So this member shows little on hiding: it shows that the premises can be
met together.
COMPLETENESS OF THE SAME HONEST SIDES is not shown here: complete_pad2,
Johnson/WholeKey/Member2Complete.lean (1/16). All at one scheme, binding idly: joined_pad2,
Johnson/WholeKey/Member2Bundle.lean.
Terms: lean/GLOSSARY.md.

-/
import Johnson.WholeKey.Member
import Hiop.Seeded.Pad2

set_option autoImplicit false

noncomputable section

open scoped ENNReal

namespace OnBytes.WholeKey.Member2
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom Prob
open OnBytes.Prover OnBytes.WholeKey
open OnBytes.WholeKey.Member (pick pick_ok we1 we2 we1_ok we2_ok)
open Hiop.Seeded.Two
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

/-- A block of 32 bits (Hiop/Seeded/Pad2.lean). -/
local notation "Blk₂" => Hiop.Seeded.Two.Blk

/-! ## Marks and wires -/

def aT : RoundSplits pad2.offline.shape := RoundSplits.allLocal [rT]
def aL : RoundSplits pad2.link.shape := RoundSplits.allLocal [rL]

/-- The carrier of the typed oracles: a leaf's body is a bit. -/
abbrev C2 : BatchProtocolWithLeafBody Empty pad2.XC := typedOracleCarrier pad2 Bool aT aL

/-- The wire of a round without an oracle: no tree, no test. -/
def wPlain {P C : Type} [Fintype C] [Nonempty C] (d : P) (a : RAnn (plainRound P C d))
    (chal : (Fin 1 → Dig 32) → C) : WireRB 32 1 (plainRound P C d) a where
  pt :=
    { finPos := inferInstanceAs (Fintype Empty)
      decPos := inferInstanceAs (DecidableEq Empty)
      ofSyms := fun _ => ()
      rd_ofSyms := fun _ p => p.elim
      ofSyms_rd := fun _ => rfl
      zero := fun p => p.elim }
  depth0 := []
  depthJ := []
  tree := fun p => p.elim
  place := fun p => p.elim
  posAt0 := fun _ _ => none
  posAtJ := fun _ _ => none
  chal := chal

/-- The wire of the first table's round: ONE TREE of depth 0 over the slot's component; its one leaf
holds the oracle's one position. No test. -/
def wT : WireRB 32 1 rT (RAnn.allLocal rT) where
  pt :=
    { finPos := inferInstanceAs (Fintype Unit)
      decPos := inferInstanceAs (DecidableEq Unit)
      ofSyms := fun f => f ()
      rd_ofSyms := fun _ _ => rfl
      ofSyms_rd := fun _ => rfl
      zero := fun _ => false }
  depth0 := []
  depthJ := [0]
  tree := fun _ => 0
  place := fun _ => 0
  posAt0 := fun _ _ => none
  posAtJ := fun k j => if k = 0 ∧ j = 0 then some () else none
  chal := fun _ => ()

/-- how the oracle's symbol is written into a leaf's body, and read back -/
def embT2 : (p : OPos [rT]) → OSym [rT] p → Bool
  | .inl _, a => a
  | .inr e, _ => nomatch e

def prjT2 : (p : OPos [rT]) → Bool → Option (OSym [rT] p)
  | .inl _, b => some b
  | .inr e, _ => nomatch e

theorem prjT2_emb : ∀ (p : OPos [rT]) (a : OSym [rT] p), prjT2 p (embT2 p a) = some a
  | .inl _, _ => rfl
  | .inr e, _ => nomatch e
def wL : WireRB 32 1 rL (RAnn.allLocal rL) := wPlain _ _ fun _ => ()

/-- The test of the session's first round: one bit, the block's first; the nonce is the number in
the plain part; tries 0, .., 3. -/
def gr : GrW Blk₂ ((Bool × Bool) × ℕ) where
  b := 1
  tst := fun c _ => c 0 0
  set := fun z c => Function.update c 0 (Function.update (c 0) 0 (z 0))
  more := 3
  put := fun k α => (α.1, k)
  get := fun α => α.2

def wB1 : WireRB 32 1 rB1 (RAnn.ofSlot .lo rB1) :=
  { (wPlain _ _ fun u => u : WireRB 32 1 rB1 (RAnn.ofSlot .lo rB1)) with grJ := some gr }

def wB2 : WireRB 32 1 rB2 (RAnn.ofShared .sh rB2) := wPlain _ _ fun _ => ()

def W2 : QueryLayout 32 C2 where
  K := 1
  T := ⟨(wT, ()), we1, inferInstanceAs (DecidableEq (OPos [rT])), 2, 0⟩
  Lk := ⟨(wL, ()), we2, fun a => (no_oposL a).elim, 2, 0⟩
  B := ⟨(wB1, (wB2, ())), we1, fun a => (no_oposB a).elim, 1, 0⟩
  depth := 0
  depthReq := 0
  depthReqT := 0
  depthReqL := 0
  embE := fun s => s
  prjE := fun b => some b
  embT := embT2
  prjT := prjT2
  embL := fun p => (no_oposL p).elim
  prjL := fun p => (no_oposL p).elim
  embB := fun p => (no_oposB p).elim
  prjB := fun p => (no_oposB p).elim

/-- The seeds' wire: at the session's Fiat-Shamir oracle; the seed is the first bit. -/
def S2 : OutOfDomainSampleQueryLayout 32 W2.K pad2 Bool aT aL where
  t := .onl
  cfg := []
  shape := []
  pl0 := .inl (.inr (((false, false), 0) : (Bool × Bool) × ℕ))
  pl1 := .inl (.inr (((false, false), 0) : (Bool × Bool) × ℕ))
  seed := fun u => (show Fin 1 → Dig 32 from u) 0 0
  code := fun rc => [fun _ => rc.1, fun _ => rc.2]
  num := fun _ _ => true
  decS := inferInstanceAs (DecidableEq Bool)

/-- An answer as one digest. -/
def cA2 : pad2.OutOfDomainAnswer → List (Dig 32) := fun a => [fun _ => a]

def p2 : Params := ⟨33, 32, 1, 2⟩

/-! ## The wires' laws -/

/-- The uniform law does not hang on how the type's members are listed. -/
theorem unif_inst {C : Type} (i₁ i₂ : Fintype C) [Nonempty C] :
    @PMF.uniformOfFintype C i₁ _ = @PMF.uniformOfFintype C i₂ _ := by
  rw [Subsingleton.elim i₁ i₂]

theorem wPlain_okg {P C : Type} [Fintype C] [Nonempty C] (d : P) (a : RAnn (plainRound P C d))
    (chal : (Fin 1 → Dig 32) → C)
    (hc : (unif (Fin 1 → Dig 32)).map chal = unif (plainRound P C d).Chal) :
    (wPlain d a chal).OKG where
  place_lt0 := fun p => Empty.elim p
  place_ltJ := fun p => Empty.elim p
  posAt0_place := fun p => Empty.elim p
  posAtJ_place := fun p => Empty.elim p
  place_posAt0 := fun _ _ _ h => by cases h
  place_posAtJ := fun _ _ _ h => by cases h
  no0 := fun _ _ _ => rfl
  noJ := fun _ _ _ => rfl
  chal_unif := hc
  gr0_ok := fun _ e => by cases e
  grJ_ok := fun _ e => by cases e

theorem unif_unit (q : PMF Unit) : q = unif Unit :=
  Prob.eq_unif_of_const _ fun b b' => by cases b; cases b'; rfl

theorem wT_okg : wT.OKG where
  place_lt0 := fun _ h => Bool.noConfusion h
  place_ltJ := fun _ _ => ⟨0, rfl, Nat.one_pos⟩
  posAt0_place := fun _ h => Bool.noConfusion h
  posAtJ_place := fun p _ => by
    show (if (0 : ℕ) = 0 ∧ (0 : ℕ) = 0 then some () else none) = some p
    rw [if_pos ⟨rfl, rfl⟩]
    rfl
  place_posAt0 := fun _ _ _ h => by cases h
  place_posAtJ := fun k j _ h => by
    by_cases hk : k = 0 ∧ j = 0
    · exact ⟨rfl, hk.1.symm, hk.2.symm⟩
    · have h' : (if k = 0 ∧ j = 0 then some () else none) = some () := h
      rw [if_neg hk] at h'
      cases h'
  no0 := fun _ _ _ => rfl
  noJ := fun k hk _ => if_neg fun h => by
    have h1 : 1 ≤ k := hk
    omega
  chal_unif := unif_unit _
  gr0_ok := fun _ e => by cases e
  grJ_ok := fun _ e => by cases e
theorem wL_okg : wL.OKG := wPlain_okg _ _ _ (unif_unit _)
theorem wB2_okg : wB2.OKG := wPlain_okg _ _ _ (unif_unit _)

theorem gr_ok : gr.OK where
  tst_set := fun (z : Fin 1 → Bool) (c : Blk₂) => by
    funext (j : Fin 1)
    show (Function.update c 0 (Function.update (c 0) 0 (z 0))) 0 0 = z j
    rw [Function.update_self, Function.update_self, Subsingleton.elim j 0]
  set_tst := fun (c : Blk₂) => by
    show Function.update c 0 (Function.update (c 0) 0 (c 0 0)) = c
    rw [Function.update_eq_self, Function.update_eq_self]
  set_set := fun (z z' : Fin 1 → Bool) (c : Blk₂) => by
    show Function.update (Function.update c 0 (Function.update (c 0) 0 (z' 0))) 0
        (Function.update ((Function.update c 0 (Function.update (c 0) 0 (z' 0))) 0) 0 (z 0)) =
      Function.update c 0 (Function.update (c 0) 0 (z 0))
    rw [Function.update_self, Function.update_idem, Function.update_idem]
  get_put := fun _ _ _ => rfl

theorem wB1_okg : wB1.OKG where
  place_lt0 := fun p => Empty.elim p
  place_ltJ := fun p => Empty.elim p
  posAt0_place := fun p => Empty.elim p
  posAtJ_place := fun p => Empty.elim p
  place_posAt0 := fun _ _ _ h => by cases h
  place_posAtJ := fun _ _ _ h => by cases h
  no0 := fun _ _ _ => rfl
  noJ := fun _ _ _ => rfl
  chal_unif := (PMF.map_id _).trans (unif_inst _ _)
  gr0_ok := fun _ e => by cases e
  grJ_ok := fun g e => by
    have e' : gr = g := Option.some.inj e
    rw [← e']
    exact gr_ok

theorem depthT : RoundsQueryLayout.DepthLe 0 [rT] aT ((wT, ()) : RoundsQueryLayout 32 1 [rT] aT) :=
  ⟨⟨fun _ h => (by cases h), fun _ h => le_of_eq (List.mem_singleton.1 h)⟩, trivial⟩

theorem depthL : RoundsQueryLayout.DepthLe 0 [rL] aL ((wL, ()) : RoundsQueryLayout 32 1 [rL] aL) :=
  ⟨⟨fun _ h => (by cases h), fun _ h => (by cases h)⟩, trivial⟩

theorem depthB :
    RoundsQueryLayout.DepthLe 0 [rB1, rB2] annB ((wB1, (wB2, ())) : RoundsQueryLayout 32 1 [rB1, rB2] annB) :=
  ⟨⟨fun _ h => (by cases h), fun _ h => (by cases h)⟩,
    ⟨fun _ h => (by cases h), fun _ h => (by cases h)⟩, trivial⟩

theorem w2_okg : W2.OKG where
  T := ⟨⟨wT_okg, trivial⟩, we1_ok, fun _ _ _ => Nat.zero_le _, depthT⟩
  Lk := ⟨⟨wL_okg, trivial⟩, we2_ok, fun _ _ _ => Nat.zero_le _, depthL⟩
  B := ⟨⟨wB1_okg, wB2_okg, trivial⟩, we1_ok, fun _ _ _ => Nat.zero_le _, depthB⟩
  fits := le_rfl
  slots := rfl
  extDepth := ⟨rfl, rfl, rfl⟩
  depthT := le_rfl
  depthL := le_rfl
  depthB := le_rfl
  extT := fun _ => ⟨rfl, rfl⟩
  extB := fun _ => ⟨rfl, rfl⟩
  extL := ⟨fun _ => ⟨rfl, rfl⟩, fun _ => ⟨rfl, rfl⟩⟩
  prjE_emb := fun _ => rfl
  prjT_emb := prjT2_emb
  prjL_emb := fun p _ => (no_oposL p).elim
  prjB_emb := fun p _ => (no_oposB p).elim

theorem okgT : (wTC W2).OKG :=
  ⟨⟨wT_okg, trivial⟩, we1_ok, fun _ _ _ => by
    show ({posT} : Finset (OPos [rT])).card + ({0} : Finset (Fin 1)).card ≤ 2
    rw [Finset.card_singleton, Finset.card_singleton], depthT⟩

theorem okgL : (wLC W2).OKG :=
  ⟨⟨wL_okg, trivial⟩, we2_ok, fun _ _ _ => by
    show (∅ : Finset (OPos [rL])).card + ({.inl 0, .inr 0} : Finset (Fin 1 ⊕ Fin 1)).card ≤ 2
    simp, depthL⟩

theorem okgB : (wBC W2).OKG :=
  ⟨⟨wB1_okg, wB2_okg, trivial⟩, we1_ok, fun _ _ _ => by
    show (∅ : Finset (OPos [rB1, rB2])).card + ({0} : Finset (Fin 1)).card ≤ 1
    simp, depthB⟩

theorem ansOK : AnsOK cA2 where
  inj := fun a a' h => by
    have h1 : (fun _ : Fin 32 => a) = fun _ => a' := List.singleton_inj.1 h
    exact congrFun h1 0
  len := fun _ _ => rfl

theorem oka : OKA W2 cA2 := ⟨w2_okg, okgT, okgL, okgB, ansOK⟩

/-! ## Honest sides and simulators -/

def recs2 : ThreeProvers pad2 := ⟨sideT _, sideL _, sideB _⟩

def sm2 : Sims pad2 := ⟨simT, simL, fun _ => simB⟩

theorem ext2 : ExtEnc recs2 := ⟨fun _ _ _ => rfl, fun _ _ _ _ _ => rfl, fun _ _ _ _ => rfl⟩

/-- The range: the two indices that are bits. -/
def ok2 : Option Bool → Prop := fun i => i ≠ none

theorem good2 (Ryes : Option Bool → Unit → Prop) :
    sm2.Good recs2 W2 ok2 (fun _ => True) Ryes 0 0 0 where
  T := fun i r e hi _ =>
    le_of_eq (pr_eq_zero_of_forall_not_mem _ fun _ _ h => h.2 (exactT (i, r, e) hi _ _))
  Lk := fun i r e r' e' hi _ _ =>
    le_of_eq (pr_eq_zero_of_forall_not_mem _ fun _ _ h =>
      h.2 (exactL (i, (r, e), (r', e')) hi _ _))
  B := fun n i r e _ hi _ _ =>
    le_of_eq (pr_eq_zero_of_forall_not_mem _ fun _ _ h => h.2 (exactB (i, r, e, n) hi _ _))

theorem stops2 (Ryes : Option Bool → Unit → Prop) :
    StopsSmall recs2 W2 ok2 (fun _ => True) Ryes 0 0 0 where
  T := fun _ _ _ hi _ => le_of_eq (pr_eq_zero_of_forall_not_mem _ fun _ _ h => hi h)
  Lk := fun _ _ _ _ _ hi _ _ => le_of_eq (pr_eq_zero_of_forall_not_mem _ fun _ _ h => hi h)
  B := fun _ _ _ _ _ hi _ _ => le_of_eq (pr_eq_zero_of_forall_not_mem _ fun _ _ h => hi h)

/-! ## The honest side's letters, the coins -/

/-- The coins that are drawn for a compiled run: 32 bits of a first salt, 32 behind the slot's
value; a window of two rounds, one tree a component, one leaf a tree, 32 free bits a leaf. -/
def co2 : Enum (Coins 32 C2) :=
  coinsPre (lam := 32) (L := C2) 2 1 1 32 32 32 0 (false : Bool) 0 [] (pick _)

theorem co2_law : RunLaw co2 2 1 1 32 32 32 0 (false : Bool) 0 :=
  runLaw_coinsPre (lam := 32) (L := C2) 2 1 1 32 32 32 0 (false : Bool) 0 [] (pick _) (pick_ok _)

def at2 : AtRecs 32 pad2 Bool aT aL where
  Hs := recs2
  dc := ⟨fun _ _ _ => Classical.dec _, fun _ _ _ => Classical.dec _, fun _ _ _ => Classical.dec _⟩
  b₀ := false
  capT := fun _ => 0
  capL := fun _ => 0
  capB := fun _ => 3
  M := 1
  nm := id
  RV := Bool
  okV := fun _ => True
  rvT := fun κ => κ
  rvL := fun κ => κ
  rvB := fun κ => κ
  startT := fun v _ _ _ => [v]
  startL := fun v _ _ _ => [v]
  startB := fun v _ _ _ => [v]
  pvT := fun pl => (show Bool × Unit from pl).1
  pvL := fun pl => (show (Bool × Bool) × Unit from pl).1.2
  pvB := fun pl => (show ((Bool × Bool) × ℕ) × (Bool × Unit) from pl).1.1.2
  rtail := fun _ => []
  nR := 2
  nK := 1
  nJ := 1
  fill := List.replicate 32 false
  ri := pick (Bool × Bool)
  sl := saltsPre [false] (2 ^ 0) 32 (pick _)
  kT := pick Bool
  kL := pick Bool
  kB := pick Bool
  coT := co2
  coL := co2
  coB := co2

def cn2 : CoinNums Bool := ⟨[false], 32, 32, false, false, false, 0, 0, 0⟩

/-- b, qT, qpar, qch, qon, s1; then all errors 0. -/
def nu2 : NumsW := ⟨3, 1, 1, 1, 1, 2, 0, 0, 0, 0, 0, 0, 0⟩

theorem coins2 : CoinsFit W2 p2 at2 cn2 where
  ri := pick_ok _
  kT := pick_ok _
  kL := pick_ok _
  kB := pick_ok _
  sl := saltsLaw_saltsPre [false] (2 ^ 0) 32 (pick _) (pick_ok _)
  len₀ := rfl
  okT := fun _ => trivial
  okL := fun _ => trivial
  okB := fun _ => trivial
  lenT := fun _ _ _ _ _ _ _ => rfl
  lenL := fun _ _ _ _ _ _ _ => rfl
  lenB := fun _ _ _ _ _ _ _ => rfl
  coT := co2_law
  coL := co2_law
  coB := co2_law
  rounds := ⟨by decide, by decide, le_rfl⟩
  winT := ⟨⟨Nat.zero_le _, le_rfl, fun _ h => (by cases h), fun d h => by
    rw [List.mem_singleton.1 h]
    exact le_rfl⟩, trivial⟩
  winL := ⟨⟨Nat.zero_le _, Nat.zero_le _, fun _ h => (by cases h), fun _ h => (by cases h)⟩,
    trivial⟩
  winB := ⟨⟨Nat.zero_le _, Nat.zero_le _, fun _ h => (by cases h), fun _ h => (by cases h)⟩,
    ⟨Nat.zero_le _, Nat.zero_le _, fun _ h => (by cases h), fun _ h => (by cases h)⟩, trivial⟩

theorem runVals2 : RunVals at2 ok2 where
  T := fun _ _ _ _ ρ _ _ => by
    obtain ⟨c, ρ'⟩ := (ρ : Unit × Unit)
    rfl
  Lk := fun _ _ _ _ ρ _ _ => by
    obtain ⟨c, ρ'⟩ := (ρ : Unit × Unit)
    rfl
  B := fun _ _ _ _ _ _ ρ _ _ => by
    obtain ⟨c, c', ρ'⟩ := (ρ : Blk₂ × Unit × Unit)
    rfl

/-! ## All premises together -/

/-- **ALL PREMISES OF THE STATEMENT OF INDEX PRIVACY HOLD TOGETHER** at these letters, for every
relation. -/
theorem premW_pad2 (Ryes : Option Bool → Unit → Prop) :
    PremW W2 S2 cA2 p2 at2 sm2 ok2 (fun _ => True) Ryes cn2 nu2 where
  ext := ext2
  runVals := runVals2
  reads := pad2_readsG 3
  budget₀ := le_rfl
  budget₁ := le_rfl
  good := good2 Ryes
  stops := stops2 Ryes
  seeds := le_of_eq (pr_eq_zero_of_forall_not_mem _ fun _ _ h => h trivial)
  freeT := fun _ _ _ _ => rfl
  freeL := fun _ _ _ _ => rfl
  freeB := fun _ _ _ _ => rfl
  wires := oka
  fmt := ⟨RoundSplits.fmt_allLocal _, RoundSplits.fmt_allLocal _, RAnn.noShared_ofSlot .lo rB1, trivial⟩
  backT := ⟨fun _ e => (by cases e), trivial⟩
  backL := ⟨fun _ e => (by cases e), trivial⟩
  backB := ⟨fun g e k α _ => by
    have e' : gr = g := Option.some.inj e
    rw [← e']
    rfl, fun _ e => (by cases e), trivial⟩
  plain := ⟨rfl, rfl⟩
  coherent := ⟨BatchOne.BAnn.allLocal_coherent _, BatchOne.BAnn.allLocal_coherent _,
    RAnn.ofSlot_coherent .lo rB1, RAnn.ofShared_coherent .sh rB2, trivial⟩
  isLocal := ⟨localT _, localL _, localB _⟩
  coins := coins2

/-! ## The error is below 1 -/

/-- The names of the typed oracles. -/
local notation "ON₂" => TypedOracleCompiler.Compile.Batch.OracleName

/-- The names at which the honest side asks a query that holds a secret string: the nine of every
scheme, and the names of the tries number 2, 3, 4 of the session's search. -/
theorem os_pad2 : osW W2 at2 =
    ({.leaf, .rleaf, .rnode, .g .test, .g .link, .g .onl, .fb .test, .fb .link, .fb .onl,
      .fbw .onl 0, .fbw .onl 1, .fbw .onl 2} : Finset ON₂) := by
  decide

/-- The hash part of the error at one query and three requests. -/
theorem hash_pad2 :
    Rom.costTotal (S := typedOracleFamily 32 W2.K C2) (eW W2 S2 at2 3) (mW W2 at2 3) (bitsW (lam := 32) p2 cn2)
      (osW W2 at2) 1 ≤ 204 / 4294967296 := by
  have key : ∑ o ∈ ({.leaf, .rleaf, .rnode, .g .test, .g .link, .g .onl, .fb .test, .fb .link,
      .fb .onl, .fbw .onl 0, .fbw .onl 1, .fbw .onl 2} : Finset ON₂),
      (mW W2 at2 3 o : ℝ≥0∞) * ((1 + eW W2 S2 at2 3 o + mW W2 at2 3 o : ℕ) : ℝ≥0∞) /
        2 ^ bitsW (lam := 32) p2 cn2 o = 204 / 4294967296 := by
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton]
    show ((4 : ℕ) : ℝ≥0∞) * ((1 + 0 + 4 : ℕ) : ℝ≥0∞) / 2 ^ 32 +
      (((6 : ℕ) : ℝ≥0∞) * ((1 + 0 + 6 : ℕ) : ℝ≥0∞) / 2 ^ 32 +
      (((0 : ℕ) : ℝ≥0∞) * ((1 + 0 + 0 : ℕ) : ℝ≥0∞) / 2 ^ 32 +
      (((1 : ℕ) : ℝ≥0∞) * ((1 + 0 + 1 : ℕ) : ℝ≥0∞) / 2 ^ 32 +
      (((2 : ℕ) : ℝ≥0∞) * ((1 + 0 + 2 : ℕ) : ℝ≥0∞) / 2 ^ 32 +
      (((3 : ℕ) : ℝ≥0∞) * ((1 + 0 + 3 : ℕ) : ℝ≥0∞) / 2 ^ 32 +
      (((1 : ℕ) : ℝ≥0∞) * ((1 + 0 + 1 : ℕ) : ℝ≥0∞) / 2 ^ 32 +
      (((2 : ℕ) : ℝ≥0∞) * ((1 + 0 + 2 : ℕ) : ℝ≥0∞) / 2 ^ 32 +
      (((6 : ℕ) : ℝ≥0∞) * ((1 + 6 + 6 : ℕ) : ℝ≥0∞) / 2 ^ 32 +
      (((3 : ℕ) : ℝ≥0∞) * ((1 + 0 + 3 : ℕ) : ℝ≥0∞) / 2 ^ 32 +
      (((3 : ℕ) : ℝ≥0∞) * ((1 + 0 + 3 : ℕ) : ℝ≥0∞) / 2 ^ 32 +
      ((3 : ℕ) : ℝ≥0∞) * ((1 + 0 + 3 : ℕ) : ℝ≥0∞) / 2 ^ 32)))))))))) = 204 / 4294967296
    simp only [ENNReal.div_add_div_same]
    norm_num
  refine (Rom.costTotal_le _ _ _ _ _).trans (le_of_eq ?_)
  unfold Rom.costNames
  rw [os_pad2]
  exact key

/-- The chance that one of the two copies is drawn for all three requests, more than it serves: at
most 1/4. -/
theorem tail_pad2 : Prob.pOver (at2.M + 1) nu2.s1 3 ≤ 1073741824 / 4294967296 := by
  refine (Prob.pOver_le_choose 2 2 3).trans (le_of_eq ?_)
  have hc : Nat.choose 3 (2 + 1) = 1 := by decide
  rw [hc, ← mul_div_assoc]
  rw [ENNReal.div_eq_div_iff (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
  norm_num

/-- **The error of the statement is below 1 at these letters**, at one query and THREE requests, one
more than a copy serves: at most 1/4 for an overrun and 204 / 2^32 for the hashes. -/
theorem zeta_pad2 : zetaW W2 S2 p2 at2 cn2 nu2 1 3 < 1 := by
  have hz : zetaW W2 S2 p2 at2 cn2 nu2 1 3 =
      Prob.pOver (at2.M + 1) nu2.s1 3 +
        Rom.costTotal (S := typedOracleFamily 32 W2.K C2) (eW W2 S2 at2 3) (mW W2 at2 3)
          (bitsW (lam := 32) p2 cn2) (osW W2 at2) 1 := by
    unfold zetaW
    show Prob.pOver (at2.M + 1) nu2.s1 3 +
      (0 + ((1 + 1 : ℕ) : ℝ≥0∞) * 0 + ((3 : ℕ) : ℝ≥0∞) * 0) +
      (0 + ((1 + 1 : ℕ) : ℝ≥0∞) * 0 + ((3 : ℕ) : ℝ≥0∞) * 0) + ((1 + 2 : ℕ) : ℝ≥0∞) * 0 + _ = _
    simp
  rw [hz]
  refine lt_of_le_of_lt (add_le_add tail_pad2 hash_pad2) ?_
  rw [ENNReal.div_add_div_same]
  refine ENNReal.div_lt_of_lt_mul ?_
  norm_num

end OnBytes.WholeKey.Member2

#print axioms OnBytes.WholeKey.Member2.zeta_pad2
#print axioms OnBytes.WholeKey.Member2.premW_pad2
