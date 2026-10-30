-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Print/Member.lean: the premises on a whole typed proof under which the goals' decoder
gives it back (`Fits`, Johnson/Prover/Print/FormBack.lean) can be met together: at all letters S, at
every configuration's digest of 32 bytes and at all records, a written whole typed proof meets them.

The written proof is bare: no opening at all, plain parts of zeros, digests of zeros, one written
run value (not zero) in all six places; the key file's front bears the key's record's own answers.

Main names (namespace `Johnson.Prover.Print`).
  `zeroS`                    plain parts of zeros for a list of rounds
  `bareW`, `bareL`           the bare string of a whole file, of the entry's file; for all data
  `printable_bareW`, `canon_bareW`, `printableL_bareL`, `sizesL_bareL`   they meet the predicates
  `bare S cm rcd copy cm' rcd'`   the bare whole typed proof at S
  `fits_bare`                c.size = 32 → copy < 2 ^ 64 → Fits S c (bare S cm rcd copy cm' rcd')

Limits. It shows that `Fits` is not empty, and no more. No verifier accepts the bare proof, or is
said to: where nothing is opened every clause on an opening holds of nothing, so the clauses on the
first bits of a leaf's typed salt are not tried by it. Nothing on `PublicS`. No prover.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Print.FormBack
import OnBytes.Flat.TableNumbers
import Fmt.Rules23Laws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Prover.Print

open VerifierAndGoals FlashProve
open VerifiableInference VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.SlotsBehindCutD
open OnBytes.Flat OnBytes.Slice OnBytes.Maker
open _root_.Run
open _root_.Iop (Dig Plains GPlain OPos OSym)
open _root_.Compile (Opening)
open TypedOracleCompiler.Compile.Batch (OneProtocolProof)
open TypedOracleCompiler.Joined (pls₁ pls₂ pls₃ opensL opensR opensL_eq opensR_eq)
open LPFD.Full (sBG sTG)
open PV.EntryFive (dsF xsF)
open OnBytes.Prover.Print (carrierOf Printable Canon CanonI CanonP CanonO RootsFit SizesFit op₁ op₂
  op₃ SaltFrom)

/-! ## Plain parts of zeros -/

/-- Plain parts of zeros; the nonce 0 where a round has work. -/
def zeroS (C : PQ.CK) : (ds : List TypedOracleCompiler.Run.PQ.RD) → Plains (TypedOracleCompiler.Run.PQ.uL C ds)
  | [] => ()
  | d :: ds => (GPlain.mk d.entry.work (PQ.PlainOf.dflt d.items) (0 : ℕ), zeroS C ds)

theorem okF_zero : Carrier.okF 0 := by
  show (0 : UInt64).toNat < _root_.Fmt.Fld.two.p
  decide

theorem okE_zero : Carrier.okE (0, 0, 0) := ⟨okF_zero, okF_zero, okF_zero⟩

theorem canonI_dflt : ∀ l : List _root_.Fmt.Item, CanonI l (PQ.PlainOf.dflt l)
  | [] => trivial
  | .root :: l => canonI_dflt l
  | .f :: l => ⟨okF_zero, canonI_dflt l⟩
  | .word :: l => canonI_dflt l
  | .e :: l => ⟨okE_zero, canonI_dflt l⟩
  | .answer :: l => ⟨okE_zero, canonI_dflt l⟩

theorem nonce_mk_zero {P : Type} : ∀ (b : ℕ) (p : P), GPlain.nonce (GPlain.mk b p (0 : ℕ)) = 0
  | 0, _ => rfl
  | _ + 1, _ => rfl

theorem canonP_zeroS (C : PQ.CK) : ∀ ds : List RDT, CanonP C ds (zeroS C (toRDs ds))
  | [] => trivial
  | d :: ds => by
    refine ⟨?_, ?_, canonP_zeroS C ds⟩
    · show CanonI d.items (GPlain.old (GPlain.mk d.entry.work (PQ.PlainOf.dflt d.items) (0 : ℕ)))
      rw [GPlain.old_mk]
      exact canonI_dflt _
    · show GPlain.nonce (GPlain.mk d.entry.work (PQ.PlainOf.dflt d.items) (0 : ℕ)) < 2 ^ 64
      rw [nonce_mk_zero]
      exact Nat.two_pow_pos 64

theorem nonces_zeroS (C : PQ.CK) : ∀ (ds : List TypedOracleCompiler.Run.PQ.RD) (rts : List (Dig 256)),
    ∀ r ∈ roundsOfS C ds rts (zeroS C ds), r.2 < 2 ^ 64
  | [], _, r, hr => nomatch hr
  | d :: ds, rts, r, hr => by
    rcases List.mem_cons.1 hr with rfl | hr
    · show GPlain.nonce (GPlain.mk d.entry.work (PQ.PlainOf.dflt d.items) (0 : ℕ)) < 2 ^ 64
      rw [nonce_mk_zero]
      exact Nat.two_pow_pos 64
    · exact nonces_zeroS C ds _ r hr

/-- the digest of zeros -/
def dig0 : Dig 256 := fun _ => false

/-! ## The bare string of a whole file -/

section
variable (C : PQ.CK) (D : WholeD) (tF : FrontMsg (List OnBytes.E))
  (tJ : Compile.Joined.JoinMsg (List OnBytes.E) ByteArray) (t3 : ByteArray) {Xi : Type}
  (silent : Xi → FrontMsg (List OnBytes.E) → Compile.Joined.JoinMsg (List OnBytes.E) ByteArray →
    ByteArray → Bool) (run : Xi → PQ.View → PQ.View → PQ.View → Bool)
  (ans : List OnBytes.E) (copy : ℕ) (r : ByteArray) (s : OnBytes.Params.LinBindingShape)

local notation "𝔉" => chainsOf C D tF tJ t3

/-- the three chains' plain parts -/
abbrev part₁ : Plains (𝔉).c₁ :=
  ((⟨ans, copy⟩ : FrontMsg (List OnBytes.E)), zeroS C (toRDs D.ds₁))

abbrev part₂ : Plains (𝔉).c₂ :=
  ((⟨ans, r⟩ : Compile.Joined.JoinMsg (List OnBytes.E) ByteArray), zeroS C (toRDs D.ds₂))

abbrev part₃ : Plains (𝔉).c₃ := (r, zeroS C (toRDs D.ds₃))

/-- No opening; plain parts of zeros; the front ⟨ans, copy⟩; the run value r in all three places. -/
def bareW : OneProtocolProof 256 (wholeDesc C D tF tJ t3 silent run).batch where
  salt := bytesToBits r
  roots := List.replicate (Carrier.treesIn D) dig0
  plains := Plains.app (s := (𝔉).c₁) (t := (𝔉).c₂ ++ (𝔉).c₃)
    (part₁ C D tF tJ t3 ans copy)
    (Plains.app (s := (𝔉).c₂) (t := (𝔉).c₃) (part₂ C D tF tJ t3 ans r) (part₃ C D tF tJ t3 r))
  opens := fun _ => none
  ext := fun _ => none
  rtreq := dig0
  slot := 0
  path := List.replicate s.logLeaves dig0
  rsalt := rsOf (2 ^ s.logLeaves + 0) (_root_.Fmt.zeroBytes s.saltBytes)

theorem pls₁_bareW : pls₁ (wholeDesc C D tF tJ t3 silent run)
    (bareW C D tF tJ t3 silent run ans copy r s) = part₁ C D tF tJ t3 ans copy :=
  Plains.fst_app (s := (𝔉).c₁) (t := (𝔉).c₂ ++ (𝔉).c₃) (part₁ C D tF tJ t3 ans copy) _

theorem pls₂_bareW : pls₂ (wholeDesc C D tF tJ t3 silent run)
    (bareW C D tF tJ t3 silent run ans copy r s) = part₂ C D tF tJ t3 ans r := by
  show Plains.fst (s := (𝔉).c₂) (t := (𝔉).c₃)
    (Plains.snd (s := (𝔉).c₁) (t := (𝔉).c₂ ++ (𝔉).c₃)
      (Plains.app (s := (𝔉).c₁) (t := (𝔉).c₂ ++ (𝔉).c₃)
        (part₁ C D tF tJ t3 ans copy)
        (Plains.app (s := (𝔉).c₂) (t := (𝔉).c₃) (part₂ C D tF tJ t3 ans r)
          (part₃ C D tF tJ t3 r)))) = _
  rw [Plains.snd_app, Plains.fst_app]

theorem pls₃_bareW : pls₃ (wholeDesc C D tF tJ t3 silent run)
    (bareW C D tF tJ t3 silent run ans copy r s) = part₃ C D tF tJ t3 r := by
  show Plains.snd (s := (𝔉).c₂) (t := (𝔉).c₃)
    (Plains.snd (s := (𝔉).c₁) (t := (𝔉).c₂ ++ (𝔉).c₃)
      (Plains.app (s := (𝔉).c₁) (t := (𝔉).c₂ ++ (𝔉).c₃)
        (part₁ C D tF tJ t3 ans copy)
        (Plains.app (s := (𝔉).c₂) (t := (𝔉).c₃) (part₂ C D tF tJ t3 ans r)
          (part₃ C D tF tJ t3 r)))) = _
  rw [Plains.snd_app, Plains.snd_app]

theorem op₁_bareW (q : OPos (uLT C D.ds₁)) :
    op₁ C D tF tJ t3 silent run (bareW C D tF tJ t3 silent run ans copy r s) q = none := by
  unfold op₁
  rw [opensL_eq]
  rfl

theorem op₂_bareW (q : OPos (uLT C D.ds₂)) :
    op₂ C D tF tJ t3 silent run (bareW C D tF tJ t3 silent run ans copy r s) q = none := by
  unfold op₂
  rw [opensL_eq, opensR_eq]
  rfl

theorem op₃_bareW (q : OPos (uLT C D.ds₃)) :
    op₃ C D tF tJ t3 silent run (bareW C D tF tJ t3 silent run ans copy r s) q = none := by
  unfold op₃
  rw [opensR_eq, opensR_eq]
  rfl

theorem printable_bareW (cfg : ByteArray) (hr : r.size = 32) :
    Printable C D tF tJ t3 silent run cfg s (bareW C D tF tJ t3 silent run ans copy r s) where
  salt := by
    show (bytesToBits r).length = 256
    rw [length_bytesToBits, hr]
  run2 := by
    rw [pls₂_bareW]
    exact hr
  run3 := by
    rw [pls₃_bareW]
    exact hr
  answers := by
    rw [pls₂_bareW, pls₁_bareW]
  roots := List.length_replicate
  own₁ := fun q op h => by
    rw [op₁_bareW] at h
    cases h
  own₂ := fun q op h => by
    rw [op₂_bareW] at h
    cases h
  own₃ := fun q op h => by
    rw [op₃_bareW] at h
    cases h
  ext := fun _ _ h => nomatch h
  slot := Nat.two_pow_pos _
  path := List.length_replicate
  rsalt := ⟨_root_.Fmt.zeroBytes s.saltBytes, _root_.Fmt.size_zeros _, rfl⟩

theorem canon_bareW (ha : ∀ e ∈ ans, Carrier.okE e.triple) (hn : ans.length < 2 ^ 64)
    (hc : copy < 2 ^ 64) :
    Canon C D tF tJ t3 silent run (bareW C D tF tJ t3 silent run ans copy r s) where
  answers := by
    rw [pls₁_bareW]
    exact ha
  count := by
    rw [pls₁_bareW]
    exact hn
  copy := by
    rw [pls₁_bareW]
    exact hc
  plain₁ := by
    rw [pls₁_bareW]
    exact canonP_zeroS C D.ds₁
  plain₂ := by
    rw [pls₂_bareW]
    exact canonP_zeroS C D.ds₂
  plain₃ := by
    rw [pls₃_bareW]
    exact canonP_zeroS C D.ds₃
  own₁ := fun q op h => by
    rw [op₁_bareW] at h
    cases h
  own₂ := fun q op h => by
    rw [op₂_bareW] at h
    cases h
  own₃ := fun q op h => by
    rw [op₃_bareW] at h
    cases h
  ext := fun _ _ h => nomatch h

theorem runOk_bareW (hk : Fmt.runOk r = true) :
    Fmt.runOk (bitsToBytes (bareW C D tF tJ t3 silent run ans copy r s).salt) = true ∧
      Fmt.runOk (pls₂ (wholeDesc C D tF tJ t3 silent run)
        (bareW C D tF tJ t3 silent run ans copy r s)).1.run = true ∧
      Fmt.runOk (pls₃ (wholeDesc C D tF tJ t3 silent run)
        (bareW C D tF tJ t3 silent run ans copy r s)).1 = true := by
  refine ⟨?_, ?_, ?_⟩
  · show Fmt.runOk (bitsToBytes (bytesToBits r)) = true
    rw [bitsToBytes_bytesToBits]
    exact hk
  · rw [pls₂_bareW]
    exact hk
  · rw [pls₃_bareW]
    exact hk

end

/-! ## The bare string of the entry's file -/

section
variable (C : PQ.CK) (ds : List TypedOracleCompiler.Run.PQ.RD) (a : ℕ) (xs : List PQ.XO) {X : Type}
  (dec : X → PQ.View → Bool) (r : ByteArray)

def bareL : OneProtocolProof 256 (linkSkeletonOfRoundData C ds a xs dec).up where
  salt := bytesToBits r
  roots := List.replicate (ds.map (·.trees.length)).sum dig0
  plains := ((), zeroS C ds)
  opens := fun _ => none
  ext := fun _ => none
  rtreq := fun _ => false
  slot := 0
  path := []
  rsalt := []

theorem printableL_bareL (cfg : ByteArray) (hr : r.size = 32) (hc : cfg.size = 32) :
    PrintableL C ds a xs dec cfg (bareL C ds a xs dec r) where
  salt := by
    show (bytesToBits r).length = 256
    rw [length_bytesToBits, hr]
  cfg32 := hc
  roots := List.length_replicate
  own := fun _ _ h => nomatch h
  ext0 := fun _ _ h => nomatch h
  ext1 := fun _ _ h => nomatch h
  rtreq := rfl
  slot := rfl
  path := rfl
  rsalt := rfl

theorem sizesL_bareL (hP : PublicL ds a) (root0 : ByteArray)
    (answers0 : List (UInt64 × UInt64 × UInt64)) (root : ByteArray)
    (answers : List (UInt64 × UInt64 × UInt64)) (h0 : root0.size = 32)
    (h1 : answers0.length < 2 ^ 64) (h2 : root.size = 32) (h3 : answers.length < 2 ^ 64) :
    SizesL C ds a xs dec root0 answers0 root answers (bareL C ds a xs dec r) where
  root0 := h0
  answers0 := h1
  root := h2
  answers := h3
  rounds := hP.rounds
  items := hP.items
  trees := hP.trees
  shapes := hP.shapes
  depth := hP.depth
  nonces := nonces_zeroS C ds _
  own := fun _ _ h => nomatch h
  ext := fun _ _ h => nomatch h

end

/-! ## The written answers -/

/-- The words of a record's written answers are below the prime. -/
theorem okE_trAns {v s : ℕ} (a : (Fin v → Bool) × Fin s → Cb.Gl.E) :
    ∀ t ∈ trAns a, Carrier.okE t := by
  intro t ht
  obtain ⟨n, rfl⟩ := (List.mem_ofFn' _ _).1 ht
  exact okE_of_okE (writeE _) (OnBytes.K.IdTable.written_okE _)

/-! ## The bare whole typed proof -/

/-- the written run value -/
def run0 : ByteArray := _root_.Fmt.pattern 32

theorem size_run0 : run0.size = 32 := by decide +kernel

theorem runOk_run0 : Fmt.runOk run0 = true := by decide +kernel

variable {Zk : OnBytes.K.Pub} (S : DescriptionDataAtFiles Zk)

/-- **The bare whole typed proof at S.** -/
def bare (cm : Dig 256) (rcd : RecFull) (copy : ℕ) (cm' : Dig 256) (rcd' : RecFull) : Typed S where
  aux := []
  cm := cm
  rcd := rcd
  copy := copy
  piT := bareW (ckP .two) (S.DK.at frS.P.T.a) (front₀ S.G.rec₀) (join₀ S.G.rec₀) ByteArray.empty
    silK S.runK ((trAns rcd.2).map OnBytes.E.ofTriple) 0 run0 (sTG S.G)
  cm' := cm'
  rcd' := rcd'
  piL := bareL (ckP .two) dsF frS.P.T.a xsF S.dec run0
  piB := bareW (ckP .two) (S.DP.at frS.P.T.a) (front₀ S.G.z₀.2) (join₀ S.G.z₀.2) ByteArray.empty
    silP S.runP [] copy run0 (sBG S.G)

theorem length_trAns_lt (rcd : RecFull) : (trAns rcd.2).length < 2 ^ 64 := by
  rw [(wf_seedsOf rcd).2.2, frS_v]
  omega

/-- **`Fits` is not empty**: at all letters, digests of 32 bytes and records. -/
theorem fits_bare (c : ByteArray) (hc : c.size = 32) (cm : Dig 256) (rcd : RecFull) (copy : ℕ)
    (hcopy : copy < 2 ^ 64) (cm' : Dig 256) (rcd' : RecFull) :
    Fits S c (bare S cm rcd copy cm' rcd') where
  c32 := hc
  prT := printable_bareW _ _ _ _ _ _ _ _ _ _ _ c size_run0
  cnT := canon_bareW _ _ _ _ _ _ _ _ _ _ _
    (fun e he => by
      obtain ⟨t, ht, rfl⟩ := List.mem_map.1 he
      exact okE_trAns _ t ht)
    (by rw [List.length_map]; exact length_trAns_lt rcd) (Nat.two_pow_pos 64)
  prB := printable_bareW _ _ _ _ _ _ _ _ _ _ _ c size_run0
  cnB := canon_bareW _ _ _ _ _ _ _ _ _ _ _ (fun _ he => nomatch he) (Nat.two_pow_pos 64) hcopy
  prL := printableL_bareL _ _ _ _ _ _ c size_run0 hc
  szL := sizesL_bareL _ _ _ _ _ _ publicL_full _ _ _ _ (size_digToBytes _) (length_trAns_lt rcd)
    (size_digToBytes _) (length_trAns_lt rcd')
  runT := runOk_bareW _ _ _ _ _ _ _ _ _ _ _ runOk_run0
  runB := runOk_bareW _ _ _ _ _ _ _ _ _ _ _ runOk_run0
  ansT := by
    show (pls₁ _ (bareW (ckP .two) (S.DK.at frS.P.T.a) (front₀ S.G.rec₀) (join₀ S.G.rec₀)
      ByteArray.empty silK S.runK ((trAns rcd.2).map OnBytes.E.ofTriple) 0 run0
      (sTG S.G))).1.answers = (trAns rcd.2).map OnBytes.E.ofTriple
    rw [pls₁_bareW]
  copyT := by
    show (pls₁ _ (bareW (ckP .two) (S.DK.at frS.P.T.a) (front₀ S.G.rec₀) (join₀ S.G.rec₀)
      ByteArray.empty silK S.runK ((trAns rcd.2).map OnBytes.E.ofTriple) 0 run0
      (sTG S.G))).1.copy = 0
    rw [pls₁_bareW]
  copyB := by
    show (pls₁ _ (bareW (ckP .two) (S.DP.at frS.P.T.a) (front₀ S.G.z₀.2) (join₀ S.G.z₀.2)
      ByteArray.empty silP S.runP [] copy run0 (sBG S.G))).1.copy = copy
    rw [pls₁_bareW]

end Johnson.Prover.Print
