-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/WholeKey/Member.lean: A MEMBER: ALL PREMISES of the statement of index privacy for the
scheme with the whole key published (PremW, Johnson/WholeKey/Premises.lean) HOLD TOGETHER at a small
object whose prover shows something and whose out-of-domain answer hangs on index, randomness and
seed.

Definitions, statements and proofs. A toy: nothing here is about the protocol of the release. This
file states no goal of the release.

Why. A clause that nothing can meet compiles in silence, and a theorem with such a premise is true
and empty. Here every clause of PremW is met at once.

THE OBJECT is pad (Hiop/Seeded/Pad.lean). The index is a bit i; the encoding's randomness two bits
(r₁, r₂); the encoded index the one symbol i + r₁; two seeds; the honest answer at the seed s is
i · s + r₂. The protocol on the first table has one round: the prover sends the symbol in the clear,
the verifier reads the symbol and compares. Link and session have no round.
THE LETTERS. Digests of 8 bits, one hash block an answer. Trees of depth 0: a table has one leaf.
Request trees of depth 0. The seed is the first bit of the block. No round has a test. One copy
(M = 0), which serves one session (s1 = 1). A leaf's salt has 8 free bits and no public start; a
run's first salt 8 bits. The honest sides: the object's own for the first table's protocol and the
link; for the session the silent one (there is no round). The range is both indices (ok := all). All
seeds are good (Gs := all), so δ = 0. All
errors of the interactive protocols' simulators and all measures of stops are 0.

Main names (namespace OnBytes.WholeKey.Member).
  aT, aL, wr, WP, SP, cAP, pP, recsP, atP, smP, cnP, nuP   the letters.
  premW_pad   ALL PREMISES TOGETHER.
  zeta_pad    the statement's error at these letters, at one query and one request, is below 1. (It
    is at most 30/256: its hash term by hash_pad; the whole by zeta_pad_le,
    Johnson/WholeKey/Main.lean.) Twice the error is at most about 0.23; an error says something only
    below one half, and to be below one half is not yet to hide (Johnson/WholeKey/Half.lean).

Limits. A toy. No round has a test, so the clauses on nonces hold for lack of a case. Link and
session have no round, so their clauses are met by empty protocols. The run values are of the type
with one member.
Terms: lean/GLOSSARY.md.

-/
import Johnson.WholeKey.Zeta
import Hiop.Seeded.GameMembers
import Iop.WireOK
import Iop.BatchWireOK
import Iop.BatchOne
import Iop.BatchFmt

set_option autoImplicit false

noncomputable section

open scoped ENNReal

namespace OnBytes.WholeKey.Member
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom Prob
open OnBytes.Prover OnBytes.WholeKey
open Hiop.Seeded (pad bitRound bitProto bitSim nilProto no_opos pad_reads pad_exact)
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

/-! ## An enumeration of a finite type, picked by choice -/

/-- An enumeration that lists each member once; its length is a name, no number that Lean could set
out to compute. -/
def pick (β : Type) [Fintype β] [Nonempty β] : Enum β :=
  (⟨Enum.ofNum β (Fintype.equivFin β), Enum.ofNum_ok β (Fintype.equivFin β)⟩ :
    ∃ e : Enum β, e.OK).choose

theorem pick_ok (β : Type) [Fintype β] [Nonempty β] : (pick β).OK :=
  (⟨Enum.ofNum β (Fintype.equivFin β), Enum.ofNum_ok β (Fintype.equivFin β)⟩ :
    ∃ e : Enum β, e.OK).choose_spec

/-! ## Marks and wires -/

/-- The one round of the first table's protocol is local. -/
def aT : RoundSplits pad.offline.shape := RoundSplits.allLocal [bitRound]

def aL : RoundSplits pad.link.shape := PUnit.unit

/-- The carrier of the typed oracles: a leaf's body is a bit. -/
abbrev CP : BatchProtocolWithLeafBody Empty pad.XC := typedOracleCarrier pad Bool aT aL

/-- The wire of the one round: no oracle, no tree, no test; the verifier message has one value. -/
def wr : WireRB 8 1 bitRound (RAnn.allLocal bitRound) where
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
  chal := fun _ => ()

/-- One word of one symbol: position 0 is leaf 0 of tree 0. -/
def we1 : WireE (oneExternalString 1 Bool) where
  all := [0]
  which := fun _ => 0
  leaf := fun p => p.val
  depth := 0
  build := fun f p => (f p).getD false
  dec := inferInstance

/-- Two such words: the first in tree 0, the second in tree 1. -/
def we2 : WireE (twoExternalStrings 1 Bool) where
  all := [.inl 0, .inr 0]
  which := fun p => Sum.elim (fun _ => 0) (fun _ => 1) p
  leaf := fun p => Sum.elim (fun q => q.val) (fun q => q.val) p
  depth := 0
  build := fun f => (fun p => (f (.inl p)).getD false, fun p => (f (.inr p)).getD false)
  dec := inferInstance

def WP : QueryLayout 8 CP where
  K := 1
  T := ⟨(wr, ()), we1, fun a => (no_opos a).elim, 1, 0⟩
  Lk := ⟨(), we2, fun a => a.elim, 0, 0⟩
  B := ⟨(), we1, fun a => a.elim, 0, 0⟩
  depth := 0
  depthReq := 0
  depthReqT := 0
  depthReqL := 0
  embE := fun s => s
  prjE := fun b => some b
  embT := fun p => (no_opos p).elim
  prjT := fun p => (no_opos p).elim
  embL := fun p => p.elim
  prjL := fun p => p.elim
  embB := fun p => p.elim
  prjB := fun p => p.elim

/-- The seeds' wire: at the first table's Fiat-Shamir oracle; the seed is the first bit. -/
def SP : OutOfDomainSampleQueryLayout 8 WP.K pad Bool aT aL where
  t := .test
  cfg := []
  shape := []
  pl0 := .inl (.inr false)
  pl1 := .inl (.inr false)
  seed := fun u => (show Fin 1 → Dig 8 from u) 0 0
  code := fun rc => [fun _ => rc.1, fun _ => rc.2]
  num := fun _ _ => true
  decS := inferInstanceAs (DecidableEq Bool)

/-- An answer as one digest. -/
def cAP : pad.OutOfDomainAnswer → List (Dig 8) := fun a => [fun _ => a]

def pP : Params := ⟨8, 8, 0, 0⟩

/-! ## The wires' laws -/

theorem wr_okg : wr.OKG where
  place_lt0 := fun p => Empty.elim p
  place_ltJ := fun p => Empty.elim p
  posAt0_place := fun p => Empty.elim p
  posAtJ_place := fun p => Empty.elim p
  place_posAt0 := fun _ _ _ h => by cases h
  place_posAtJ := fun _ _ _ h => by cases h
  no0 := fun _ _ _ => rfl
  noJ := fun _ _ _ => rfl
  chal_unif := Prob.eq_unif_of_const _ fun b b' => by cases b; cases b'; rfl
  gr0_ok := fun _ e => by cases e
  grJ_ok := fun _ e => by cases e

theorem we1_ok : we1.OK where
  nodup := List.nodup_singleton _
  complete := fun p => by
    rw [Subsingleton.elim p (0 : Fin 1)]
    exact List.mem_singleton.2 rfl
  build_rd := fun f p a h => by
    show (f p).getD false = a
    rw [h]
    rfl

theorem we2_ok : we2.OK where
  nodup := by
    show ([.inl 0, .inr 0] : List (Fin 1 ⊕ Fin 1)).Nodup
    decide
  complete := fun p => by
    cases p with
    | inl q =>
      rw [Subsingleton.elim q (0 : Fin 1)]
      exact List.Mem.head _
    | inr q =>
      rw [Subsingleton.elim q (0 : Fin 1)]
      exact List.Mem.tail _ (List.Mem.head _)
  build_rd := fun f p a h => by
    cases p with
    | inl q =>
      show (f (.inl q)).getD false = a
      rw [h]
      rfl
    | inr q =>
      show (f (.inr q)).getD false = a
      rw [h]
      rfl

theorem depthLe_wr : RoundsQueryLayout.DepthLe 0 [bitRound] aT ((wr, ()) : RoundsQueryLayout 8 1 [bitRound] aT) :=
  ⟨⟨fun _ h => (by cases h), fun _ h => (by cases h)⟩, trivial⟩

theorem wp_okg : WP.OKG where
  T := ⟨⟨wr_okg, trivial⟩, we1_ok, fun _ _ _ => Nat.zero_le _, depthLe_wr⟩
  Lk := ⟨trivial, we2_ok, fun _ _ _ => Nat.zero_le _, trivial⟩
  B := ⟨trivial, we1_ok, fun _ _ _ => Nat.zero_le _, trivial⟩
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
  prjT_emb := fun p _ => (no_opos p).elim
  prjL_emb := fun p _ => Empty.elim p
  prjB_emb := fun p _ => Empty.elim p

theorem okgT : (wTC WP).OKG :=
  ⟨⟨wr_okg, trivial⟩, we1_ok, fun _ _ _ => by
    show (∅ : Finset (OPos [bitRound])).card + ({0} : Finset (Fin 1)).card ≤ 1
    simp, depthLe_wr⟩

theorem okgL : (wLC WP).OKG := ⟨trivial, we2_ok, fun _ _ _ => Nat.zero_le _, trivial⟩

theorem okgB : (wBC WP).OKG := ⟨trivial, we1_ok, fun _ _ _ => Nat.zero_le _, trivial⟩

theorem ansOK : AnsOK cAP where
  inj := fun a a' h => by
    have h1 : (fun _ : Fin 8 => a) = fun _ => a' := List.singleton_inj.1 h
    exact congrFun h1 0
  len := fun _ _ => rfl

theorem oka : OKA WP cAP := ⟨wp_okg, okgT, okgL, okgB, ansOK⟩

/-! ## Honest sides and simulators -/

/-- The session's honest side: there is no round; its external string is the encoded index. -/
def nilB : Honest pad.onlineBatch.loc (Bool × pad.EncodingRandomness × pad.OutOfDomainSeed × ℕ) where
  Coin := Unit
  ext := fun w _ => xor w.1 w.2.1.1
  strat := fun _ _ _ => ()
  Bad := ∅
  Hid := fun _ _ => ∅

/-- The honest sides: the object's own for the first table's protocol, which sends the symbol, and
for the link. -/
def recsP : ThreeProvers pad := ⟨pad.honestOfflineProver, pad.honestLinkProver, nilB⟩

/-- The simulator of a protocol without rounds: it shows the symbols that it is handed. -/
def nilSim {Y : Type} {E : ExtSpec} :
    Y → (ρ : Rho (nilProto Y E).shape) → (E.Pos → Option E.Sym) →
      PMF (Option (DView (nilProto Y E))) :=
  fun _ _ ans => PMF.pure (some ⟨(), ans, fun p => Empty.elim p⟩)

/-- It is exact for every honest side that never stops. -/
theorem output_nil {Y Wt : Type} {E : ExtSpec} (H : Honest (nilProto Y E) Wt) (hB : H.Bad = ∅)
    (hH : ∀ w y, H.Hid w y = ∅) (w : Wt) (y : Y) (ρ : Rho (nilProto Y E).shape) :
    H.output w y ρ = nilSim y ρ ((nilProto Y E).extAns y ρ (H.ext w)) := by
  unfold Honest.output
  have hm : ρ ∉ H.withheld w y := by
    unfold Honest.withheld
    rw [hB, hH]
    simp
  have hc : (fun c : H.Coin =>
      some ((nilProto Y E).dview y (H.ext w) ((H.strat w y c).run ρ).1)) =
      Function.const _ (some ⟨(), (nilProto Y E).extAns y ρ (H.ext w), fun p => Empty.elim p⟩) := by
    funext c
    refine congrArg some ?_
    show (⟨_, _, _⟩ : DView (nilProto Y E)) = ⟨_, _, _⟩
    congr 1
    funext p
    exact Empty.elim p
  rw [if_neg hm, hc, PMF.map_const]
  rfl

def smP : Sims pad := ⟨bitSim, nilSim, fun _ => nilSim⟩

theorem ext_pad : ExtEnc recsP := ⟨fun _ _ _ => rfl, fun _ _ _ _ _ => rfl, fun _ _ _ _ => rfl⟩

theorem good_pad (Ryes : Bool → Unit → Prop) :
    smP.Good recsP WP (fun _ => True) (fun _ => True) Ryes 0 0 0 where
  T := fun i r e _ _ =>
    le_of_eq (pr_eq_zero_of_forall_not_mem _ fun _ _ h => h.2 (pad_exact (i, r, e) _ _))
  Lk := fun _ _ _ _ _ _ _ _ =>
    le_of_eq (pr_eq_zero_of_forall_not_mem _ fun _ _ h =>
      h.2 (output_nil pad.honestLinkProver rfl (fun _ _ => rfl) _ _ _))
  B := fun n _ _ _ _ _ _ _ =>
    le_of_eq (pr_eq_zero_of_forall_not_mem _ fun _ _ h =>
      h.2 (output_nil (sessionAt recsP n) rfl (fun _ _ => rfl) _ _ _))

theorem stops_pad (Ryes : Bool → Unit → Prop) :
    StopsSmall recsP WP (fun _ => True) (fun _ => True) Ryes 0 0 0 where
  T := fun _ _ _ _ _ =>
    le_of_eq (pr_eq_zero_of_forall_not_mem _ fun _ _ h => Bool.noConfusion (show false = true from
    h))
  Lk := fun _ _ _ _ _ _ _ _ => le_of_eq (pr_eq_zero_of_forall_not_mem _ fun _ _ h => h)
  B := fun _ _ _ _ _ _ _ _ => le_of_eq (pr_eq_zero_of_forall_not_mem _ fun _ _ h => h)

/-! ## The honest side's letters, the coins -/

/-- The coins that are drawn for a compiled run: 8 bits of a first salt, 8 behind the slot's value;
no tree, so no leaf. -/
def coP : Enum (Coins 8 CP) :=
  coinsPre (lam := 8) (L := CP) 1 0 0 8 8 8 0 (false : Bool) 0 [] (pick _)

theorem coP_law : RunLaw coP 1 0 0 8 8 8 0 (false : Bool) 0 :=
  runLaw_coinsPre (lam := 8) (L := CP) 1 0 0 8 8 8 0 (false : Bool) 0 [] (pick _) (pick_ok _)

def atP : AtRecs 8 pad Bool aT aL where
  Hs := recsP
  dc := ⟨fun _ _ _ => Classical.dec _, fun _ _ _ => Classical.dec _, fun _ _ _ => Classical.dec _⟩
  b₀ := false
  capT := fun _ => 0
  capL := fun _ => 0
  capB := fun _ => 0
  M := 0
  nm := id
  RV := Unit
  okV := fun _ => True
  rvT := fun _ => ()
  rvL := fun _ => ()
  rvB := fun _ => ()
  startT := fun _ _ _ _ => []
  startL := fun _ _ _ _ => []
  startB := fun _ _ _ _ => []
  pvT := fun _ => ()
  pvL := fun _ => ()
  pvB := fun _ => ()
  rtail := fun _ => []
  nR := 1
  nK := 0
  nJ := 0
  fill := List.replicate 8 false
  ri := pick (Bool × Bool)
  sl := saltsPre [] (2 ^ 0) 8 (pick _)
  kT := (⟨0, fun _ => ()⟩ : Enum Unit)
  kL := (⟨0, fun _ => ()⟩ : Enum Unit)
  kB := (⟨0, fun _ => ()⟩ : Enum Unit)
  coT := coP
  coL := coP
  coB := coP

def cnP : CoinNums Bool := ⟨[], 8, 8, false, false, false, 0, 0, 0⟩

/-- b, qT, qpar, qch, qon, s1; then all errors 0. -/
def nuP : NumsW := ⟨1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩

theorem coins_pad : CoinsFit WP pP atP cnP where
  ri := pick_ok _
  kT := BatchWireOK.enumUnit_ok
  kL := BatchWireOK.enumUnit_ok
  kB := BatchWireOK.enumUnit_ok
  sl := saltsLaw_saltsPre [] (2 ^ 0) 8 (pick _) (pick_ok _)
  len₀ := rfl
  okT := fun _ => trivial
  okL := fun _ => trivial
  okB := fun _ => trivial
  lenT := fun _ _ _ _ _ _ _ => rfl
  lenL := fun _ _ _ _ _ _ _ => rfl
  lenB := fun _ _ _ _ _ _ _ => rfl
  coT := coP_law
  coL := coP_law
  coB := coP_law
  rounds := ⟨le_rfl, Nat.zero_le _, Nat.zero_le _⟩
  winT := ⟨⟨le_rfl, le_rfl, fun _ h => (by cases h), fun _ h => (by cases h)⟩, trivial⟩
  winL := trivial
  winB := trivial

theorem isLocal_test : pad.offline.IsLocal := by
  intro x y y' τ τ' _ hpl hext _
  show (Hiop.Seeded.bitOfTr τ == (show Fin 1 → Bool from y) 0) =
    (Hiop.Seeded.bitOfTr τ' == (show Fin 1 → Bool from y') 0)
  have h1 : Hiop.Seeded.bitOfTr τ = Hiop.Seeded.bitOfTr τ' := congrArg Prod.fst hpl
  have h2 : (show Fin 1 → Bool from y) 0 = (show Fin 1 → Bool from y') 0 :=
    hext (0 : Fin 1) (Finset.mem_singleton_self (0 : Fin 1))
  rw [h1, h2]

/-! ## All premises together -/

/-- **ALL PREMISES OF THE STATEMENT OF INDEX PRIVACY HOLD TOGETHER** at these letters, for every
relation. -/
theorem premW_pad (Ryes : Bool → Unit → Prop) :
    PremW WP SP cAP pP atP smP (fun _ => True) (fun _ => True) Ryes cnP nuP where
  ext := ext_pad
  runVals := ⟨fun _ _ _ _ _ _ _ => rfl, fun _ _ _ _ _ _ _ => rfl, fun _ _ _ _ _ _ _ _ _ => rfl⟩
  reads := Hiop.Seeded.pad_readsG
  budget₀ := le_rfl
  budget₁ := Nat.zero_le _
  good := good_pad Ryes
  stops := stops_pad Ryes
  seeds := le_of_eq (pr_eq_zero_of_forall_not_mem _ fun _ _ h => h trivial)
  freeT := fun _ _ _ _ => rfl
  freeL := fun _ _ _ _ => rfl
  freeB := fun _ _ _ _ => rfl
  wires := oka
  fmt := ⟨RoundSplits.fmt_allLocal _, trivial, trivial⟩
  backT := ⟨fun _ e => (by cases e), trivial⟩
  backL := trivial
  backB := trivial
  plain := ⟨rfl, rfl⟩
  coherent := ⟨BatchOne.BAnn.allLocal_coherent _, trivial, trivial⟩
  isLocal := ⟨isLocal_test, fun _ _ _ _ _ _ _ _ _ => rfl, fun _ _ _ _ _ _ _ _ _ => rfl⟩
  coins := coins_pad

/-! ## The error is below 1 -/

/-- The names of the typed oracles. -/
local notation "ON₂" => TypedOracleCompiler.Compile.Batch.OracleName

theorem os_pad : osW WP atP =
    ({.leaf, .rleaf, .rnode, .g .test, .g .link, .g .onl, .fb .test, .fb .link, .fb .onl} :
      Finset ON₂) := by
  decide

/-- The hash part of the error at one query and one request. -/
theorem hash_pad :
    Rom.costTotal (S := typedOracleFamily 8 WP.K CP) (eW WP SP atP 1) (mW WP atP 1) (bitsW (lam := 8) pP cnP)
      (osW WP atP) 1 ≤ 30 / 256 := by
  have key : ∑ o ∈ ({.leaf, .rleaf, .rnode, .g .test, .g .link, .g .onl, .fb .test, .fb .link,
      .fb .onl} : Finset ON₂),
      (mW WP atP 1 o : ℝ≥0∞) * ((1 + eW WP SP atP 1 o + mW WP atP 1 o : ℕ) : ℝ≥0∞) /
        2 ^ bitsW (lam := 8) pP cnP o = 30 / 256 := by
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton]
    show ((2 : ℕ) : ℝ≥0∞) * ((1 + 0 + 2 : ℕ) : ℝ≥0∞) / 2 ^ 8 +
      (((3 : ℕ) : ℝ≥0∞) * ((1 + 0 + 3 : ℕ) : ℝ≥0∞) / 2 ^ 8 +
      (((0 : ℕ) : ℝ≥0∞) * ((1 + 0 + 0 : ℕ) : ℝ≥0∞) / 2 ^ 8 +
      (((1 : ℕ) : ℝ≥0∞) * ((1 + 0 + 1 : ℕ) : ℝ≥0∞) / 2 ^ 8 +
      (((1 : ℕ) : ℝ≥0∞) * ((1 + 0 + 1 : ℕ) : ℝ≥0∞) / 2 ^ 8 +
      (((1 : ℕ) : ℝ≥0∞) * ((1 + 0 + 1 : ℕ) : ℝ≥0∞) / 2 ^ 8 +
      (((1 : ℕ) : ℝ≥0∞) * ((1 + 4 + 1 : ℕ) : ℝ≥0∞) / 2 ^ 8 +
      (((0 : ℕ) : ℝ≥0∞) * ((1 + 0 + 0 : ℕ) : ℝ≥0∞) / 2 ^ 8 +
      ((0 : ℕ) : ℝ≥0∞) * ((1 + 0 + 0 : ℕ) : ℝ≥0∞) / 2 ^ 8))))))) = 30 / 256
    simp only [ENNReal.div_add_div_same]
    norm_num
  refine (Rom.costTotal_le _ _ _ _ _).trans (le_of_eq ?_)
  unfold Rom.costNames
  rw [os_pad]
  exact key

/-- **The error of the statement is below 1 at these letters**, at one query and one request: it is
at most 30/256. -/
theorem zeta_pad : zetaW WP SP pP atP cnP nuP 1 1 < 1 := by
  have hT : Prob.pOver (atP.M + 1) nuP.s1 1 = 0 := by
    show Prob.pOver 1 1 1 = 0
    unfold Prob.pOver
    rw [Prob.binTail_eq_sum_Icc]
    simp
  have hz : zetaW WP SP pP atP cnP nuP 1 1 =
      Rom.costTotal (S := typedOracleFamily 8 WP.K CP) (eW WP SP atP 1) (mW WP atP 1)
        (bitsW (lam := 8) pP cnP) (osW WP atP) 1 := by
    unfold zetaW
    rw [hT]
    show (0 : ℝ≥0∞) + (0 + ((0 + 1 : ℕ) : ℝ≥0∞) * 0 + ((1 : ℕ) : ℝ≥0∞) * 0) +
      (0 + ((0 + 1 : ℕ) : ℝ≥0∞) * 0 + ((1 : ℕ) : ℝ≥0∞) * 0) + ((0 + 2 : ℕ) : ℝ≥0∞) * 0 + _ = _
    simp
  rw [hz]
  refine lt_of_le_of_lt hash_pad ?_
  refine ENNReal.div_lt_of_lt_mul ?_
  norm_num

end OnBytes.WholeKey.Member

#print axioms OnBytes.WholeKey.Member.premW_pad
#print axioms OnBytes.WholeKey.Member.zeta_pad
