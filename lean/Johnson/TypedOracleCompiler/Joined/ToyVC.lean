-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/TypedOracleCompiler/Joined/ToyVC.lean: a test: one small interface with records at which every hypothesis of
index binding of the verifier with records (Johnson/TypedOracleCompiler/Joined/TopVC.lean) is proved, and the
theorem applied with nothing left open.

Statements on the verifier with records, over the second form of the compiler's verifier side, for a
key file's and a proof file's three hash chains, joined by seals. That this verifier writes what is
hashed as the prover's files have it is not shown in this folder.
By a reading of the programs' text it does not: behind the roots, `VC`
(Johnson/TypedOracleCompiler/RecCompile/Cms.lean) puts a code of the whole record, the seed too, into the first
query of each of its three compiled verifiers, while the programs hash the roots and the answers,
and recompute the seeds from the roots (so too the verifier written in Lean:
OnBytes/Params/Chains.lean; OnBytes/Key/Table.lean). `verifyAtFullKey` (Johnson/TypedOracleCompiler/RecCompile/CmsAns.lean) is
the form that has the answers alone there; nothing in this file is stated for it.

The key's file and the proof's file are those of Johnson/TypedOracleCompiler/Joined/ToyVCFiles.lean: three joined
hash chains each. The index is one bit. A record is a seed, which is a hash block of one bit, and an
answer, which is the index. The link has no round: it accepts exactly the pairs of records of its
language.

Main names:
  `pLk`, `LR`       the link; the interface with records
  `WR`, `SR`        the wire record of the whole; the wire record of the seeds
  `wr_okg`, `okc`   their laws
  `noneColl`, `rcd`, `sndL`, `isLocalLk`, `hSd`   the hypotheses on the record, the link and the
                   seeds: one seed of the two is a collision seed, so the error of a query is 1/2
  `tieT`, `tieB`    the two files' languages against the decoder
  `AR`             a scheme whose verifier is the verifier with records
  `toy_binding`    the theorem `binding_of_files_late`, applied: no hypothesis is left
  `rn_speaks`      the relation holds of some index and instance and fails of some
  `one_le_epsC`    the bound of `toy_binding` is at least 1

Limits: a test, and of one thing alone: that the hypotheses of `binding_of_files_late` can be met
together, at an interface whose key and proof are three joined chains each, with a record, an
instance of which one bit enters the session's chain in a later query (`late := some 1`), and a
relation that is neither empty nor full. The other form of the theorem, `binding_of_files`, where no
later query takes in more of the instance, is not applied here. IT SHOWS NOTHING ON THE NUMBER: hash
values have one bit here, so the bound is at least 1 (`one_le_epsC`), and a bound of at least 1 on a
probability holds of every scheme. All errors of the two files are 0. Four things are met emptily:
the link has no round; there is no external string; the test on the number of the stored copy always
says yes (`SR.num`); a table's name holds its root alone (`SR.cfg`, `SR.shape`). Every type of
witnesses is Unit: so the side of knowledge is met emptily, and `tieB` is proved from the verifier's
yes alone, without its premise on the extractors' witness. The seed is the block itself, so it is
exactly uniform; a real sampler has a bias. The committer and the prover of `AR` are idle. Nothing
is run, and it is not shown that the verifier accepts anything.

Terms: lean/GLOSSARY.md.

-/
import Johnson.TypedOracleCompiler.Joined.ToyVCFiles
import Johnson.TypedOracleCompiler.Joined.TopVC

set_option autoImplicit false

noncomputable section

namespace TypedOracleCompiler.Joined.Toy
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom Prob
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Compile.Joined (Chains Desc)
open scoped ENNReal

/-! ## The interface with records -/

/-- the language of the link: the first record decodes to nothing, or the further one has a
collision seed, or both decode to the same -/
def linkLg (rr : Rec0 × Rec0) : Prop := dec0 rr.1 = none ∨ coll0 rr.2.1 ∨ dec0 rr.2 = dec0 rr.1

instance (rr : Rec0 × Rec0) : Decidable (linkLg rr) :=
  inferInstanceAs (Decidable (_ ∨ _ ∨ _))

/-- The link: a protocol without rounds, which accepts exactly its language. -/
@[reducible] def pLk : InteractiveOracleProof (Rec0 × Rec0) (twoExternalStrings 0 Unit) where
  shape := []
  blinded := fun _ => false
  extReads := fun _ _ => ∅
  reads := fun _ _ _ => ∅
  accept := fun rr _ _ => decide (linkLg rr)

/-- The interface with records: the key's file in the place of the offline protocol, the proof's
file in the place of a session; two slots; the first query of a session holds `early x`, the query
of round 1 holds x. -/
@[reducible] def LR : HolographicProtocol Bool Y2 where
  wordLength := 0
  Symbol := Unit
  EncodingRandomness := Unit
  encodeIndex := fun _ _ _ => ()
  OutOfDomainSeed := Seed0
  OutOfDomainAnswer := Bool
  honestOutOfDomainAnswer := fun i _ _ => i
  hasCollisionAt := fun _ s => coll0 s
  decodeIndex := fun _ r => dec0 r
  offline := DT.proto
  link := pLk
  maxBatchSize := 2
  onlineBatch := DB.batch
  honestOfflineProver := _root_.Run.dummyH DT.proto fun _ _ => ()
  honestLinkProver := _root_.Run.dummyH pLk fun _ => (fun _ => (), fun _ => ())
  honestOnlineBatchProver := _root_.Run.dummyB DB.batch fun _ _ => ()
  early := early
  late := some 1

/-! ## The wire records -/

/-- the body of a leaf: a position with its symbol, or nothing -/
abbrev Bd0 : Type := Option (Σ p : OPos G.sh, OSym G.sh p)

/-- how a symbol is read back from a leaf -/
def prj0 (p : OPos G.sh) (b : Bd0) : Option (OSym G.sh p) :=
  match b with
  | some z => if h : z.1 = p then some (h ▸ z.2) else none
  | none => none

theorem we2_ok : we2.OK :=
  ⟨List.nodup_nil, fun p => p.elim (fun q => q.elim0) fun q => q.elim0,
    fun _ p => p.elim (fun q => q.elim0) fun q => q.elim0⟩

/-- The wire record of the whole: blocks of one bit, one block a query. The binding tree of the key
has depth 0, that of a session depth 1, for two slots. -/
@[reducible] def WR : QueryLayout 1 (typedOracleCarrier LR Bd0 G.ann PUnit.unit) where
  K := 1
  T := ⟨V.sh, we1, decO, 2, 1⟩
  Lk := ⟨(), we2, inferInstanceAs (DecidableEq Empty), 0, 0⟩
  B := ⟨V.sh, we1, decO, 2, 1⟩
  depth := 0
  depthReq := 1
  depthReqT := 0
  depthReqL := 0
  embE := fun _ => none
  prjE := fun _ => some ()
  embT := fun p a => some ⟨p, a⟩
  prjT := prj0
  embL := fun p => nomatch p
  prjL := fun p => nomatch p
  embB := fun p a => some ⟨p, a⟩
  prjB := prj0

theorem card_reads_le (ρ : Rho G.sh) :
    (({p₁ ρ, p₃ ρ} : Finset (OPos G.sh))).card + (∅ : Finset (Fin 0)).card ≤ 2 := by
  rw [Finset.card_empty, Nat.add_zero]
  exact Finset.card_le_two

theorem wr_okg : WR.OKG where
  T := ⟨V.sh_okg V_okg, we1_ok, fun _ _ _ => Nat.zero_le _, V.sh_depthLe V_depthLe⟩
  Lk := ⟨trivial, we2_ok, fun _ _ _ => Nat.zero_le _, trivial⟩
  B := ⟨V.sh_okg V_okg, we1_ok, fun _ _ _ => Nat.zero_le _, V.sh_depthLe V_depthLe⟩
  fits := Nat.zero_le _
  slots := rfl
  extDepth := ⟨rfl, rfl, rfl⟩
  depthT := Nat.zero_le _
  depthL := Nat.zero_le _
  depthB := Nat.zero_le _
  extT := fun p => p.elim0
  extB := fun p => p.elim0
  extL := ⟨fun p => p.elim0, fun p => p.elim0⟩
  prjE_emb := fun _ => rfl
  prjT_emb := fun _ _ => dif_pos rfl
  prjL_emb := fun p => nomatch p
  prjB_emb := fun _ _ => dif_pos rfl

/-- The wire record of the seeds: a seed is the block itself; a record is written as two digests. -/
@[reducible] def SR : OutOfDomainSampleQueryLayout 1 WR.K LR Bd0 G.ann PUnit.unit where
  t := .onl
  cfg := []
  shape := []
  pl0 := .inl (.inr ())
  pl1 := .inl (.inr ())
  seed := id
  code := fun r => [r.1 0, fun _ => r.2]
  num := fun _ _ => true
  decS := inferInstance

theorem sr_ok : SR.OK where
  inj := fun r r' h => by
    have h' : [r.1 0, fun _ => r.2] = [r'.1 0, fun _ => r'.2] := h
    simp only [List.cons.injEq, and_true] at h'
    refine Prod.ext (funext fun i => ?_) (congrFun h'.2 0)
    obtain rfl : i = 0 := Subsingleton.elim _ _
    exact h'.1
  len := fun _ _ => rfl

theorem okc : OKC WR SR where
  base := wr_okg
  T := ⟨V.sh_okg V_okg, we1_ok, fun _ ρ _ => card_reads_le ρ, V.sh_depthLe V_depthLe⟩
  Lk := ⟨trivial, we2_ok, fun _ _ _ => Nat.zero_le _, trivial⟩
  B := ⟨V.sh_okg V_okg, we1_ok, fun _ ρ _ => card_reads_le ρ, V.sh_depthLe V_depthLe⟩
  seed := sr_ok

/-! ## The hypotheses on the record and the link -/

/-- the relation: the first bit of the instance is the index, the second is true -/
def Rn (i : Bool) (x : Y2) (_ : Unit) : Prop := x.1 = i ∧ x.2 = true

theorem noneColl (y : Fin 0 → Unit) (rec : LR.Rec) (h : LR.hasCollisionAt y rec.1) : LR.decodeIndex y rec = none :=
  dec0_of_coll h

/-- one seed of the two is a collision seed -/
theorem rcd (y : Fin 0 → Unit) : cnt (fun s => LR.hasCollisionAt y s) ≤ 1 :=
  cnt_le_one fun a b ha hb => funext fun i => funext fun j => by
    obtain rfl : i = 0 := Subsingleton.elim _ _
    obtain rfl : j = 0 := Subsingleton.elim _ _
    exact (show a 0 0 = true from ha).trans (show b 0 0 = true from hb).symm

theorem sndL : LR.link.Sound
    (fun rr y => LR.decodeIndex y.1 rr.1 = none ∨ LR.hasCollisionAt y.2 rr.2.1 ∨ LR.decodeIndex y.2 rr.2 = LR.decodeIndex y.1 rr.1)
    () :=
  fun rr _ h => decide_eq_false (p := linkLg rr) h

theorem isLocalLk : LR.link.IsLocal := fun _ _ _ _ _ _ _ _ _ => rfl

theorem card_seed0 : Fintype.card Seed0 = 2 := by decide

/-- the seed of a uniform block is a collision seed with probability at most 1/2 -/
theorem hSd : SR.Law (1 / 2) := fun y => by
  have h := (pr_unif_le_iff_cnt_le (fun s : Seed0 => coll0 s) 1).2 (rcd y)
  rw [card_seed0] at h
  simpa using h

/-! ## The ties of the two files' languages to the decoder -/

theorem tieT (rec : LR.Rec) (y : (oneExternalString 0 Unit).Str) (h : CT.Lg id rec y) :
    LR.hasCollisionAt y rec.1 ∨ LR.decodeIndex y rec ≠ none := by
  refine Or.inr ?_
  show dec0 rec ≠ none
  rw [dec0_of_not_coll ((lgT_iff rec y).1 h)]
  exact Option.some_ne_none _

theorem tieB (x : Y2) (rec : LR.Rec) (y : (oneExternalString 0 Unit).Str) (τ : Tr G.sh)
    (h : DB.accept (x, rec) y τ = true) : LR.relB Rn rec x y () := by
  cases hc : rec.1 0 0 with
  | true => exact Or.inl (dec0_of_coll hc)
  | false => exact Or.inr ⟨rec.2, dec0_of_not_coll hc, r0B_of_accept h⟩

/-! ## The numbers -/

theorem below_err0 (c : ℝ≥0∞) : ∀ s : Shape, Err.Below (err0 s) c
  | [] => trivial
  | _ :: s => ⟨by rw [Nat.cast_zero]; exact zero_le _, below_err0 c s⟩

/-! ## A scheme with this verifier, and the theorem -/

/-- lengths of salts and the like: all 0 -/
def p0 : Params := ⟨0, 0, 0, 0⟩

/-- A scheme whose verifier is the verifier with records; its committer and its prover are idle. -/
def AR : ZKCP.Gen.Arg (typedOracleFamily 1 WR.K (typedOracleCarrier LR Bd0 G.ann PUnit.unit)) Bool Y2 Unit
    (FullKey 1 LR G.ann PUnit.unit) Unit (RequestProof 1 LR) where
  C := fun _ => OComp.pure (⟨fun _ => false, (fun _ _ => false, false), none, []⟩, ())
  P := fun _ b => OComp.pure ⟨b.map fun _ => ⟨0, 0, none⟩, List.length_map _⟩
  V := VC WR SR p0

/-- **Every hypothesis of index binding is met at this interface**: the theorem of
Johnson/TypedOracleCompiler/Joined/TopVC.lean, applied with nothing left open. -/
theorem toy_binding :
    ZKCP.Gen.HasIndexBindingWith
      (relPair (fun i x => ∃ w, Rn i x w) (fun i x => ∃ w, Rn i x w) fun _ _ h => h)
      AR (extractorC0 WR) (epsC WR (1 / 2)) :=
  binding_of_files_late LR DT DB (CT := CT) (CB := CB) Rn Rn (fun _ _ _ => ()) 1 () rfl rfl (1 / 2)
    (fun _ _ h => h) WR SR p0 1 rfl noneColl rcd sndL knowsT decidesT tieT laws knowsB decidesB
    early_idem Nat.one_pos (Nat.le_refl 1) (fun x rec y τ h _ => tieB x rec y τ h) hSd
    (below_err0 _ G.sh) trivial (below_err0 _ G.sh) HEq.rfl laws isLocalT isLocalLk isLocalB trivial
    okc AR rfl

/-- the relation holds somewhere and fails somewhere -/
theorem rn_speaks : Rn true (true, true) () ∧ ¬ Rn false (true, true) () :=
  ⟨⟨rfl, rfl⟩, fun h => Bool.noConfusion h.1⟩

/-- At hash values of one bit the bound says nothing: it is at least 1, whatever the error of a
query. -/
theorem one_le_epsC (εs : ℝ≥0∞) (tC tP : ℕ) : 1 ≤ epsC WR εs tC tP := by
  unfold epsC
  refine le_trans ?_ le_add_self
  rw [pow_one, mul_comm, mul_div_assoc, ENNReal.div_self two_ne_zero ENNReal.ofNat_ne_top, mul_one]
  refine one_le_pow₀ ?_
  exact_mod_cast Nat.le_add_left 1 (tC + tP + tVC WR + 1)

end TypedOracleCompiler.Joined.Toy
