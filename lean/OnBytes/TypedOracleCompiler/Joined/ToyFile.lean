-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Joined/ToyFile.lean: a test: a small file with three joined chains, made to have two
features of a real file (a tree that is read at two lists; a later chain that opens an earlier
chain's tree), written out in full, with the laws of its parts proved.

OnBytes/TypedOracleCompiler/ holds the verifier side of the compiler beneath `innerCompiledVerifier`. It is
made for a key file's and a proof file's three hash chains, joined by seals; that it writes what is
hashed as the prover's files have it is not shown in this folder.

The rounds: the front | one local round | the joining round | one shared round | the seam | one
local round. Chain 1's round sends a string of two bits under one tree and one more bit under a
second tree, so its message holds two roots, and draws a hash block; chain 2's round sends a string
of two bits under one tree in the shared component and draws a hash block; chain 3's round sends
nothing and draws a hash block. The instance is one bit x. The verifier accepts if x is true and
chain 1's string holds true at two places: the place that chain 1's own block names, and the place
that chain 3's block names. So chain 1's first tree is read at two lists, and chain 3 opens a tree
that chain 1 has sent.

Main names:
  `G`, `D`          the rounds; the file's verifier. `laws`, `isLocal`.
  `mem_reads₁`, `mem_reads₃`   the two places are read; `p₃` is a place of chain 1's round that
                   depends on chain 3's block alone.
  `accepts`, `rejects`       the verifier accepts somewhere and rejects somewhere.
  `L`, `W`          the interface record and the wire record: blocks of one bit, two slots.
  `V`, `V_okg`, `wq`, `wq_okg`   the rounds' wire records and their laws. In the rounds that draw a
                   block the verifier message IS the block.
  `F`, `R`          the file as it is written into queries, and the read-back with its laws.

Limits: a test. There are no external strings (their length is 0). The front, the joining round and
the seam send and draw nothing: no seal is written. Chain 2's string and the one more bit of chain
1's round are read by nobody. Blocks have one bit: so no bound at this file is below 1 (the Limits
of OnBytes/TypedOracleCompiler/Joined/Toy.lean). Nothing here is run, and no trace is built.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Joined.Bound
import OnBytes.TypedOracleCompiler.Joined.WireOf
import Run.PlanQS

set_option autoImplicit false

noncomputable section

namespace TypedOracleCompiler.Joined.Toy
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch Rom Prob
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Compile.Joined (Chains Desc)

/-! ## The rounds -/

/-- hash blocks: one block of one bit -/
abbrev Blk : Type := Fin 1 → Dig 1

/-- a round that sends nothing and draws nothing -/
@[reducible] def rN : Round where
  Orc := Unit
  Pos := Empty
  Sym := fun _ => Unit
  rd := fun _ p => nomatch p
  Plain := Unit
  Chal := Unit
  dOrc := ()
  dPlain := ()

/-- a round that sends a string of two bits and draws a block -/
@[reducible] def rA : Round where
  Orc := Fin 2 → Bool
  Pos := Fin 2
  Sym := fun _ => Bool
  rd := fun o p => o p
  Plain := Unit
  Chal := Blk
  dOrc := fun _ => false
  dPlain := ()

/-- a round that sends a string of two bits and one more bit, and draws a block -/
@[reducible] def rB : Round where
  Orc := (Fin 2 → Bool) × Bool
  Pos := Fin 2 ⊕ Unit
  Sym := fun _ => Bool
  rd := fun o p => match p with
    | .inl j => o.1 j
    | .inr _ => o.2
  Plain := Unit
  Chal := Blk
  dOrc := (fun _ => false, false)
  dPlain := ()

/-- a round that sends nothing and draws a block -/
@[reducible] def rC : Round where
  Orc := Unit
  Pos := Empty
  Sym := fun _ => Unit
  rd := fun _ p => nomatch p
  Plain := Unit
  Chal := Blk
  dOrc := ()
  dPlain := ()

/-- The rounds of the file. -/
@[reducible] def G : Chains where
  rF := rN
  s₁ := [rB]
  rJ := rN
  s₂ := [rA]
  r3 := rN
  s₃ := [rC]
  aJ := RAnn.ofSlot .sh rN

theorem laws : G.Laws := ⟨rfl, RAnn.ofSlot_coherent .sh rN⟩

instance decO : DecidableEq (OPos G.sh) :=
  inferInstanceAs (DecidableEq
    (Empty ⊕ ((Fin 2 ⊕ Unit) ⊕ (Empty ⊕ (Fin 2 ⊕ (Empty ⊕ (Empty ⊕ Empty)))))))

/-! ## The verifier -/

/-- the place that a block names -/
def bit (b : Blk) : Fin 2 := if b 0 0 then 1 else 0

/-- a place of chain 1's string, as a position of the whole -/
def pos₁ (j : Fin 2) : OPos G.sh := G.i₁ (.inl (.inl j))

/-- the place of chain 1's string that chain 1's own block names -/
def p₁ (ρ : Rho G.sh) : OPos G.sh := pos₁ (bit (G.rho₁ ρ).1)

/-- the place of chain 1's string that chain 3's block names -/
def p₃ (ρ : Rho G.sh) : OPos G.sh := pos₁ (bit (G.rho₃ ρ).1)

/-- chain 1's string -/
def str₁ (τ : Tr G.sh) : Fin 2 → Bool := (G.tr₁ τ).1.1.1

theorem read_pos₁ (τ : Tr G.sh) (j : Fin 2) : τ.read (pos₁ j) = str₁ τ j := rfl

/-- The file's verifier: x is true, and chain 1's string holds true at both places. -/
@[reducible] def D : Desc G Bool (oneExternalString 0 Unit) where
  blinded := fun _ => false
  extReads := fun _ _ => ∅
  reads := fun _ ρ _ => {p₁ ρ, p₃ ρ}
  accept := fun x _ τ =>
    x && str₁ τ (bit (G.rho₁ τ.rho).1) && str₁ τ (bit (G.rho₃ τ.rho).1)

theorem mem_reads₁ (x : Bool) (ρ : Rho G.sh) (pl : Plains G.sh) : p₁ ρ ∈ D.reads x ρ pl :=
  Finset.mem_insert_self _ _

theorem mem_reads₃ (x : Bool) (ρ : Rho G.sh) (pl : Plains G.sh) : p₃ ρ ∈ D.reads x ρ pl :=
  Finset.mem_insert_of_mem (Finset.mem_singleton_self _)

theorem isLocal : D.proto.IsLocal := by
  intro x y y' τ τ' hρ _ _ hr
  have h1 : str₁ τ (bit (G.rho₁ τ.rho).1) = str₁ τ' (bit (G.rho₁ τ.rho).1) :=
    hr _ (mem_reads₁ x τ.rho τ.plains)
  have h3 : str₁ τ (bit (G.rho₃ τ.rho).1) = str₁ τ' (bit (G.rho₃ τ.rho).1) :=
    hr _ (mem_reads₃ x τ.rho τ.plains)
  show (x && str₁ τ (bit (G.rho₁ τ.rho).1) && str₁ τ (bit (G.rho₃ τ.rho).1)) =
    (x && str₁ τ' (bit (G.rho₁ τ'.rho).1) && str₁ τ' (bit (G.rho₃ τ'.rho).1))
  rw [h1, h3, hρ]

/-- a transcript: chain 1's string is o, every block is b -/
def trOf (o : Fin 2 → Bool) (b : Blk) : Tr G.sh :=
  (((), ()), (), (((o, false), ()), b, (((), ()), (), ((fun _ => false, ()), b, (((), ()), (),
    (((), ()), b, ()))))))

theorem accepts : D.accept true (fun p => p.elim0) (trOf (fun _ => true) fun _ _ => false) = true :=
  rfl

theorem rejects (y : (oneExternalString 0 Unit).Str) (τ : Tr G.sh) : D.accept false y τ = false := rfl

theorem rejects' :
    D.accept true (fun p => p.elim0) (trOf (fun _ => false) fun _ _ => false) = false := rfl

/-! ## The interface record -/

/-- a protocol without rounds, in the place of Test -/
@[reducible] def pT : InteractiveOracleProof Unit (oneExternalString 0 Unit) where
  shape := []
  blinded := fun _ => false
  extReads := fun _ _ => ∅
  reads := fun _ _ _ => ∅
  accept := fun _ _ _ => true

/-- a protocol without rounds, in the place of Link -/
@[reducible] def pK : InteractiveOracleProof Unit (twoExternalStrings 0 Unit) where
  shape := []
  blinded := fun _ => false
  extReads := fun _ _ => ∅
  reads := fun _ _ _ => ∅
  accept := fun _ _ _ => true

/-- The interface record: the file stands in the place of the batch protocol; two slots; the first
query holds the whole instance. The body of a leaf is a position with its symbol, or nothing. -/
@[reducible] def L : BatchProtocolWithLeafBody Unit Bool where
  wordLength := 0
  Symbol := Unit
  EncodingRandomness := Unit
  encodeIndex := fun _ _ _ => ()
  decodeIndex := fun _ => some ()
  offline := pT
  link := pK
  maxBatchSize := 2
  onlineBatch := D.batch
  honestOfflineProver := _root_.Run.dummyH pT fun _ _ => ()
  honestLinkProver := _root_.Run.dummyH pK fun _ => (fun _ => (), fun _ => ())
  honestOnlineBatchProver := _root_.Run.dummyB D.batch fun _ _ => ()
  early := id
  late := none
  Bd := Option (Σ p : OPos G.sh, OSym G.sh p)
  annT := PUnit.unit
  annL := PUnit.unit

/-! ## The wire records of the rounds -/

/-- the string of a round without a position -/
def ptN : rN.IsPoint where
  finPos := inferInstanceAs (Fintype Empty)
  decPos := inferInstanceAs (DecidableEq Empty)
  ofSyms := fun _ => ()
  rd_ofSyms := fun _ p => nomatch p
  ofSyms_rd := fun _ => rfl
  zero := fun p => nomatch p

def ptC : rC.IsPoint where
  finPos := inferInstanceAs (Fintype Empty)
  decPos := inferInstanceAs (DecidableEq Empty)
  ofSyms := fun _ => ()
  rd_ofSyms := fun _ p => nomatch p
  ofSyms_rd := fun _ => rfl
  zero := fun p => nomatch p

/-- the string of two bits -/
def ptA : rA.IsPoint where
  finPos := inferInstanceAs (Fintype (Fin 2))
  decPos := inferInstanceAs (DecidableEq (Fin 2))
  ofSyms := fun f => f
  rd_ofSyms := fun _ _ => rfl
  ofSyms_rd := fun _ => rfl
  zero := fun _ => false

/-- the string of two bits and one more bit -/
def ptB : rB.IsPoint where
  finPos := inferInstanceAs (Fintype (Fin 2 ⊕ Unit))
  decPos := inferInstanceAs (DecidableEq (Fin 2 ⊕ Unit))
  ofSyms := fun f => (fun j => f (.inl j), f (.inr ()))
  rd_ofSyms := fun _ p => match p with
    | .inl _ => rfl
    | .inr _ => rfl
  ofSyms_rd := fun _ => rfl
  zero := fun _ => false

/-- the places of one tree of depth 1, which has the number 0 -/
def at2 (k j : ℕ) : Option (Fin 2) :=
  if k = 0 then (if h : j < 2 then some ⟨j, h⟩ else none) else none

theorem at2_val (p : Fin 2) : at2 0 p.val = some p := by
  unfold at2
  rw [if_pos rfl, dif_pos p.isLt]

theorem at2_eq_some {k j : ℕ} {p : Fin 2} (h : at2 k j = some p) : 0 = k ∧ p.val = j := by
  unfold at2 at h
  split at h
  · rename_i hk
    split at h
    · cases h
      exact ⟨hk.symm, rfl⟩
    · cases h
  · cases h

theorem at2_none {k : ℕ} (hk : 1 ≤ k) (j : ℕ) : at2 k j = none := by
  unfold at2
  rw [if_neg (by omega)]

/-- a round without a position and without a draw, under any annotation -/
def wN (a : RAnn rN) : WireRB 1 1 rN a where
  pt := ptN
  depth0 := []
  depthJ := []
  tree := fun _ => 0
  place := fun _ => 0
  posAt0 := fun _ _ => none
  posAtJ := fun _ _ => none
  chal := fun _ => ()

theorem wN_okg (a : RAnn rN) : (wN a).OKG where
  place_lt0 := fun p => nomatch p
  place_ltJ := fun p => nomatch p
  posAt0_place := fun p => nomatch p
  posAtJ_place := fun p => nomatch p
  place_posAt0 := fun _ _ p => nomatch p
  place_posAtJ := fun _ _ p => nomatch p
  no0 := fun _ _ _ => rfl
  noJ := fun _ _ _ => rfl
  chal_unif := by
    rw [map_unif_eq_unif_iff]
    intro d
    simp [cnt]
  gr0_ok := fun _ h => nomatch h
  grJ_ok := fun _ h => nomatch h

/-- chain 3's round: no position; the verifier message is the block -/
def wC : WireRB 1 1 rC (RAnn.allLocal rC) where
  pt := ptC
  depth0 := []
  depthJ := []
  tree := fun _ => 0
  place := fun _ => 0
  posAt0 := fun _ _ => none
  posAtJ := fun _ _ => none
  chal := id

theorem wC_okg : wC.OKG where
  place_lt0 := fun p => nomatch p
  place_ltJ := fun p => nomatch p
  posAt0_place := fun p => nomatch p
  posAtJ_place := fun p => nomatch p
  place_posAt0 := fun _ _ p => nomatch p
  place_posAtJ := fun _ _ p => nomatch p
  no0 := fun _ _ _ => rfl
  noJ := fun _ _ _ => rfl
  chal_unif := PMF.map_id _
  gr0_ok := fun _ h => nomatch h
  grJ_ok := fun _ h => nomatch h

/-- the places of two trees: number 0, of depth 1, over the two bits; number 1, of depth 0, over the
one more bit -/
def at3 (k j : ℕ) : Option (Fin 2 ⊕ Unit) :=
  if k = 1 then (if j = 0 then some (.inr ()) else none) else (at2 k j).map .inl

/-- the number of the tree of a position of chain 1's round -/
def tree3 : Fin 2 ⊕ Unit → ℕ
  | .inl _ => 0
  | .inr _ => 1

/-- its place in that tree -/
def place3 : Fin 2 ⊕ Unit → ℕ
  | .inl i => i.val
  | .inr _ => 0

theorem at3_eq_some {k j : ℕ} {p : Fin 2 ⊕ Unit} (h : at3 k j = some p) :
    tree3 p = k ∧ place3 p = j := by
  unfold at3 at h
  split at h
  · rename_i hk
    split at h
    · rename_i hj
      cases h
      exact ⟨hk.symm, hj.symm⟩
    · cases h
  · obtain ⟨i, hi, rfl⟩ := Option.map_eq_some_iff.1 h
    exact at2_eq_some hi

theorem at3_none {k : ℕ} (hk : 2 ≤ k) (j : ℕ) : at3 k j = none := by
  unfold at3
  rw [if_neg (by omega), at2_none (by omega)]
  rfl

/-- chain 1's round: TWO trees over the slot's component, of depths 1 and 0, so its message holds
two roots; the verifier message is the block -/
def wA₁ : WireRB 1 1 rB (RAnn.allLocal rB) where
  pt := ptB
  depth0 := []
  depthJ := [1, 0]
  tree := tree3
  place := place3
  posAt0 := fun _ _ => none
  posAtJ := at3
  chal := id

theorem wA₁_okg : wA₁.OKG where
  place_lt0 := fun _ h => nomatch h
  place_ltJ := fun p _ => match p with
    | .inl i => ⟨1, rfl, i.isLt⟩
    | .inr _ => ⟨0, rfl, Nat.one_pos⟩
  posAt0_place := fun _ h => nomatch h
  posAtJ_place := fun p _ => match p with
    | .inl i => by
      show at3 0 i.val = some (.inl i)
      unfold at3
      rw [if_neg (by omega), at2_val]
      rfl
    | .inr _ => rfl
  place_posAt0 := fun _ _ _ h => nomatch h
  place_posAtJ := fun _ _ _ h => ⟨rfl, at3_eq_some h⟩
  no0 := fun _ _ _ => rfl
  noJ := fun _ hk j => at3_none hk j
  chal_unif := PMF.map_id _
  gr0_ok := fun _ h => nomatch h
  grJ_ok := fun _ h => nomatch h

/-- chain 2's round: the same tree over the shared component -/
def wA₂ : WireRB 1 1 rA (RAnn.ofShared .sh rA) where
  pt := ptA
  depth0 := [1]
  depthJ := []
  tree := fun _ => 0
  place := fun p => p.val
  posAt0 := at2
  posAtJ := fun _ _ => none
  chal := id

theorem wA₂_okg : wA₂.OKG where
  place_lt0 := fun p _ => ⟨1, rfl, p.isLt⟩
  place_ltJ := fun _ h => nomatch h
  posAt0_place := fun p _ => at2_val p
  posAtJ_place := fun _ h => nomatch h
  place_posAt0 := fun _ _ _ h => ⟨rfl, at2_eq_some h⟩
  place_posAtJ := fun _ _ _ h => nomatch h
  no0 := fun _ hk j => at2_none hk j
  noJ := fun _ _ _ => rfl
  chal_unif := PMF.map_id _
  gr0_ok := fun _ h => nomatch h
  grJ_ok := fun _ h => nomatch h

/-- The wire records of the file's parts. -/
def V : Wires 1 1 G where
  wF := wN _
  W₁ := (wA₁, ())
  wJ := wN _
  W₂ := (wA₂, ())
  w3 := wN _
  W₃ := (wC, ())

theorem V_okg : V.OKG where
  wF := wN_okg _
  W₁ := ⟨wA₁_okg, trivial⟩
  wJ := wN_okg _
  W₂ := ⟨wA₂_okg, trivial⟩
  w3 := wN_okg _
  W₃ := ⟨wC_okg, trivial⟩

theorem le_nil (d : ℕ) : ∀ e ∈ ([] : List ℕ), e ≤ d := fun _ h => nomatch h

theorem le_one : ∀ e ∈ [1], e ≤ 1 := fun _ h => le_of_eq (List.mem_singleton.1 h)

theorem le_one_zero : ∀ e ∈ [1, 0], e ≤ 1 := by decide

theorem V_depthLe : V.DepthLe 1 where
  wF := ⟨le_nil 1, le_nil 1⟩
  W₁ := ⟨⟨le_nil 1, le_one_zero⟩, trivial⟩
  wJ := ⟨le_nil 1, le_nil 1⟩
  W₂ := ⟨⟨le_one, le_nil 1⟩, trivial⟩
  w3 := ⟨le_nil 1, le_nil 1⟩
  W₃ := ⟨⟨le_nil 1, le_nil 1⟩, trivial⟩

/-- the wire record of external strings of length 0 -/
def we1 : WireE (oneExternalString 0 Unit) where
  all := []
  which := fun p => p.elim0
  leaf := fun p => p.elim0
  depth := 0
  build := fun _ p => p.elim0
  dec := inferInstanceAs (DecidableEq (Fin 0))

theorem we1_ok : we1.OK := ⟨List.nodup_nil, fun p => p.elim0, fun _ p => p.elim0⟩

def we2 : WireE (twoExternalStrings 0 Unit) where
  all := []
  which := fun p => p.elim (fun q => q.elim0) fun q => q.elim0
  leaf := fun p => p.elim (fun q => q.elim0) fun q => q.elim0
  depth := 0
  build := fun _ => (fun p => p.elim0, fun p => p.elim0)
  dec := inferInstanceAs (DecidableEq (Fin 0 ⊕ Fin 0))

/-- The wire record of the file's protocol: at most two openings, in trees of depth at most 1. -/
def wq : ProtocolQueryLayout 1 1 D.batch := V.qb D we1 decO 2 1

theorem wq_okg : wq.OKG :=
  V.qb_okg D we1 decO 2 1 V_okg we1_ok
    (fun _ _ _ => by
      show (({_, _} : Finset (OPos G.sh))).card + (∅ : Finset (Fin 0)).card ≤ 2
      rw [Finset.card_empty, Nat.add_zero]
      exact Finset.card_le_two)
    V_depthLe

/-- The wire record of the whole: blocks of one bit, one block a query; the request tree of the
file's tag has depth 1, for two slots. -/
@[reducible] def W : QueryLayout 1 L where
  K := 1
  T := ⟨(), we1, inferInstanceAs (DecidableEq Empty), 0, 0⟩
  Lk := ⟨(), we2, inferInstanceAs (DecidableEq Empty), 0, 0⟩
  B := wq
  depth := 0
  depthReq := 1
  depthReqT := 0
  depthReqL := 0
  embE := fun _ => none
  prjE := fun _ => some ()
  embT := fun p => nomatch p
  prjT := fun p => nomatch p
  embL := fun p => nomatch p
  prjL := fun p => nomatch p
  embB := fun p a => some ⟨p, a⟩
  prjB := fun p b => match b with
    | some z => if h : z.1 = p then some (h ▸ z.2) else none
    | none => none

/-! ## The file as it is written -/

/-- The file as it is written into the queries: under the tag of the batch protocol; a symbol is
written with its position; plain parts and the instance are written as they are. -/
@[reducible] def F : FileW W G Bool (oneExternalString 0 Unit) where
  D := D
  t := .onl
  wq := wq
  embS := fun p a => some ⟨p, a⟩
  embP := fun z => z
  xin := some
  embE := fun _ => none

/-- how a symbol of an external string is read back from a leaf -/
def prjE : Body L → Option (oneExternalString 0 Unit).Sym := fun _ => some ()

theorem prjE_emb (a : (oneExternalString 0 Unit).Sym) : prjE (F.embE a) = some a := rfl

/-- The read-back of what the file writes. -/
def R : ReadBack F.written id where
  prjS := fun p b => match b with
    | some z => if h : z.1 = p then some (h ▸ z.2) else none
    | none => none
  prjP := some
  xout := id
  prjS_emb := fun _ _ => dif_pos rfl
  prjP_emb := fun _ => rfl
  xout_in := fun _ _ => rfl

end TypedOracleCompiler.Joined.Toy
