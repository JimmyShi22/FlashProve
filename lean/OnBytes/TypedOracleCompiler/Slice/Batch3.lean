-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Slice/Batch3.lean: the batch's generic protocol over the sibling: a front round, first
stretch (local) ‖ joining round, second stretch (shared) ‖ third stretch (local); a list of trees a
round; one stored table; an instance; any decision.
Related text: Ior/BatchSeq.lean states, by its own head, rules for a batch as links in a row (local
rounds: the same errors; the joining round: N times; shared rounds: the same errors; in a row): the
shape of the joint law. The compiler under OnBytes/TypedOracleCompiler/ is the one that `innerCompiledVerifier` is
made with; it builds on definitions of Compile/.
This file is written general: three lists of
rounds' data, the front as data, the joining round's annotation a parameter; the number of slots is
the interface's. It stands on Plain3 (OnBytes/TypedOracleCompiler/Slice/Plain3.lean: a protocol over a list of trees
a round): the shape is Plain3's with its first seam replaced by a front round and without its second
seam; Plain3's verifier looks at no seam, so views, tests and what is asked are Plain3's own, at the
transcript with the first two seams' fixed messages put back (toTr).
The seam s1 is out of the shape, for this reason (found by reading the format's texts and the calls'
bytes; not proved): a proof file has no call that would be s1's query (F2) without a root, once (G)
is SEAL 1's call: between the first chain's last round but one and the binding tree's leaf a proof
file has one call of the chain, SEAL 1's: that is (G). The matching that follows is inferred from
the format's texts and from the calls' bytes; it is not proved (every match, 48,290 and 48,388 are
inferred; that SEAL 1 is the first chain's last round is read off the blocks' text, not off a
print): (F1) = the first chain's first call 160; (G) = the written round SEAL 1's call 162 (its
second half is the seal); (F4) = the shared chain's first call 160; (F5) = its rounds' 162 (70, SEAL
2 among them); (F3) = the second chain's first call 160; so: 1 + 48,290 + 1 + 70 + 1 + 25 = 48,388
typed rounds at the full size: front | chain 1 less SEAL | the joining round | chain 2 | s3 | chain
3.
  Front  a front round as data: a point round with one verifier message (named, so that a wiring
      computes), and how its positions lie in trees. Front.Laws: the laws of that lying.
  Front.silent  a seam as a front: nothing is sent in an oracle (the entry, the key, a plain chain)
  Front.one' T P t p  one oracle of one position, in a tree of depth 0 (for the request's words),
      with a plain part in P
  BD  the data: Plain3's G, the first two seams' one verifier messages c0, c1 (for a type alone), a
      front F, the joining round's annotation aJ of kind .sh (G.s2 is the joining round; G.s0 and
      G.s1 are dead fields that a builder must still fill; G.s3 is the local seam behind the shared
      block)
  BD.sh, toTr, toRho, toPl, posB  the shape and the carryings to Plain3's; rho_toTr, plains_toTr,
      posB_left, posB_right
  Batch3 D dec  the local protocol of one slot: InteractiveOracleProof X (one stored table): the verifier reads every
      position of the front and what Plain3 reads; it accepts if Plain3's three tests pass on each
      stretch and dec says yes to the instance, the front's symbols, the front's plain part and the
      three views
  BD.ann  the annotation: front and first stretch local; the joining round aJ; the second stretch
      shared (only the shared part is sent); G.s3 and the third stretch local
  BatchP D dec  the batch protocol ⟨Batch3 D dec, D.ann⟩
  batch3_local  the verifier is local, for every decision
  ann_coherent  the annotation is coherent, if aJ is
  ann_localTo  the front and the first stretch are local rounds: every round up to number n ≤ the
      first stretch's length (what "late" asks; if the request's words are sent through Front.one',
      late must be none: the late query holds the whole instance, so the words in clear)
  annLo_eq_app, annSh_eq_app  the two makers of annotations are the library's RoundSplits.app at
      RoundSplits.allLocal | RoundSplits.const (RAnn.ofShared .sh): the library's lemmas and tools are stated at
      these
By reading actOf | recomputeChain, and by evaluation at a toy (a file of this project that is not in this
library): front: fb .f1 | first
stretch: fb .f2 | s2: g, then fb .f4 | second stretch: fb .f5 | s3: fb .f3 | third stretch: fb .f2;
at the end the request tree; the verifier refuses the annotation nowhere.
Facts about the proof file that other files must meet; none is this file's matter. For the page that
spells queries as calls: (G)'s answer is the second half of SEAL 1's call, its first half is used by
nobody; in (F3) the place of ρ₀ holds SEAL 2's seal, not the shared chain's running value. For the
typing (a checker that asks the oracle; no pure parser gives it): in the file the request tree is
climbed before the shared chain begins, the root computed; each later first call holds a run value
more (they ride in the seams' plain parts: so F's aJ must have a shared plain part). For the
compiled verifier, which follows the byte format as it ships: the request tree's leaf is salted and
holds its slot (173): reqCheck asks rleaf at the slot value with OneProtocolProof's field rsalt behind it;
(F5)'s call holds no outer root: Head.f5 holds none. The two partial codes: two files of this
project that are not in this library; no page yet. The matching holds at `answers = 0`
alone: at a table with answers, a
fourth chain (label 2^32: one first call, one round) stands between the binding tree and the shared
chain's first call: between (G) and (F4), which are one typed round here.
What is not said. No wiring (Slice/Batch3Wire.lean). That the annotation has the library's form (Sh)
(OneBlock) and its working form RoundSplits.Fmt (both are believed to hold; neither is built). No seam's
plain part, the joining round's two among them, reaches the decision (they are hashed). BatchP is a
InteractiveOracleProof over Round | Shape, no skeleton (Twin.PS): the evaluable verifier verifyP and thin_verify do
not apply to it as it lies (inherited from Plain3). The frame's "the table's positions are a
function of the shared verifier messages" fails as soon as xs₁ or xs₃ opens. One toy goes through
this file (a file of this project that is not in this library). SEAL 1 is no round of ds₁: the first
view has one round fewer than the
program's block closes: dec's builder must know. hJ is used by no theorem yet. Nothing on soundness:
no state function, no error. That any file's three chains are such a protocol: which rounds the
lists hold is not fixed here. How the compiled chain's queries (F1) to (F5), (G) and the request
tree are spelled as the format's calls. The decision sees the front's symbols and the instance: that
it compares them is the instance's matter.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Slice.Plain3Local

set_option autoImplicit false

namespace TypedOracleCompiler.Slice
open _root_.Iop TypedOracleCompiler.Run

/-! ## The front round -/

/-- A front round, as data. -/
structure Front where
  r : Round
  pt : r.IsPoint
  /-- it has one verifier message -/
  one : Subsingleton r.Chal
  /-- that message -/
  c : r.Chal
  /-- the depths of its trees, in the order of their roots -/
  depths : List ℕ
  tree : r.Pos → ℕ
  place : r.Pos → ℕ
  posAt : ℕ → ℕ → Option r.Pos

/-- how the front's positions lie in its trees: the laws -/
structure Front.Laws (F : Front) : Prop where
  place_lt : ∀ p, ∃ d, F.depths[F.tree p]? = some d ∧ F.place p < 2 ^ d
  posAt_place : ∀ p, F.posAt (F.tree p) (F.place p) = some p
  place_posAt : ∀ k j p, F.posAt k j = some p → F.tree p = k ∧ F.place p = j
  no : ∀ k, F.depths.length ≤ k → ∀ j, F.posAt k j = none

/-- A seam as a front: no oracle. -/
@[reducible] def Front.silent (s : Seam) (c : s.r.Chal) : Front where
  r := s.r
  pt := { finPos := @Fintype.ofIsEmpty _ s.noPos
          decPos := fun p _ => (s.noPos.false p).elim
          ofSyms := fun _ => s.r.dOrc
          rd_ofSyms := fun _ p => (s.noPos.false p).elim
          ofSyms_rd := fun _ => s.noOrc.elim _ _
          zero := fun p => (s.noPos.false p).elim }
  one := s.one
  c := c
  depths := []
  tree := fun _ => 0
  place := fun _ => 0
  posAt := fun _ _ => none

theorem Front.silent_laws (s : Seam) (c : s.r.Chal) : (Front.silent s c).Laws where
  place_lt := fun p => (s.noPos.false p).elim
  posAt_place := fun p => (s.noPos.false p).elim
  place_posAt := fun _ _ _ h => by cases h
  no := fun _ _ _ => rfl

/-- One oracle of one position, in a tree of depth 0, and a plain part. t and p are the fixed
message that every round has to name. -/
@[reducible] def Front.one' (T P : Type) (t : T) (p : P) : Front where
  r := { Orc := T, Pos := Unit, Sym := fun _ => T, rd := fun o _ => o, Plain := P, Chal := Unit, dOrc := t, dPlain := p }
  pt := { finPos := (inferInstance : Fintype Unit)
          decPos := (inferInstance : DecidableEq Unit)
          ofSyms := fun f => f ()
          rd_ofSyms := fun _ _ => rfl
          ofSyms_rd := fun _ => rfl
          zero := fun _ => t }
  one := (inferInstance : Subsingleton Unit)
  c := ()
  depths := [0]
  tree := fun _ => 0
  place := fun _ => 0
  posAt := fun k j => if k = 0 ∧ j = 0 then some () else none

theorem Front.one_laws (T P : Type) (t : T) (p : P) : (Front.one' T P t p).Laws where
  place_lt := fun _ => ⟨0, rfl, Nat.zero_lt_one⟩
  posAt_place := fun _ => rfl
  place_posAt := fun k j _ h => by
    simp only at h
    split_ifs at h with hc
    exact ⟨hc.1.symm, hc.2.symm⟩
  no := fun k hk j => by
    have hk' : 1 ≤ k := hk
    exact if_neg fun hc => by omega

/-! ## The data -/

/-- The public data of a batch's local protocol. -/
structure BD where
  /-- three stretches, their seams, the stored table: Plain3's data. G.s0 AND G.s1 ARE NOT IN THE
  SHAPE: the front stands in the place of the first; the second has no call in a proof file -/
  G : Stretches
  /-- the first seam's one verifier message: with it a transcript is carried to Plain3's shape -/
  c0 : G.s0.r.Chal
  /-- the second seam's: the same -/
  c1 : G.s1.r.Chal
  /-- the front round -/
  F : Front
  /-- the joining round's annotation -/
  aJ : RAnn G.s2.r
  /-- it is a shared round (else the second stretch's first round would silently become the joining
  round) -/
  hJ : aJ.kind = Kind.sh

namespace BD
variable (D : BD)

/-- THE JOINING ROUND, the second stretch, and what follows -/
abbrev shJ : Shape := D.G.s2.r :: (PQ.uL D.G.C D.G.ds₂ ++ D.G.sh₃)

/-- The shape: front, first stretch, JOINING ROUND, second stretch, seam, third stretch:
Plain3's with the front in the place of its first seam and WITHOUT its second. -/
abbrev sh : Shape := D.F.r :: (PQ.uL D.G.C D.G.ds₁ ++ D.shJ)

instance decO : DecidableEq (OPos D.sh) := by
  haveI := D.F.pt.decPos
  haveI : DecidableEq (OPos (PQ.uL D.G.C D.G.ds₁ ++ D.shJ)) :=
    decApp D.G.C _ (decSeam _ _ (decApp D.G.C _ (decSeam _ _ (PQ.decSL D.G.C D.G.ds₃)) D.G.ds₂))
        D.G.ds₁
  exact inferInstanceAs (DecidableEq (D.F.r.Pos ⊕ OPos (PQ.uL D.G.C D.G.ds₁ ++ D.shJ)))

/-- a transcript, carried to Plain3's shape: the first two seams' fixed messages and their one
verifier messages are put in -/
def toTr (τ : Tr D.sh) : Tr D.G.sh :=
  ((D.G.s0.r.dOrc, D.G.s0.r.dPlain), D.c0,
    Tr.app (t := D.G.sh₂) (Tr.fst τ.2.2) ((D.G.s1.r.dOrc, D.G.s1.r.dPlain), D.c1,
        Tr.snd (s := PQ.uL D.G.C D.G.ds₁) τ.2.2))
def toRho (ρ : Rho D.sh) : Rho D.G.sh :=
  (D.c0, Rho.app (t := D.G.sh₂) (Rho.fst ρ.2) (D.c1, Rho.snd (s := PQ.uL D.G.C D.G.ds₁) ρ.2))
def toPl (π : Plains D.sh) : Plains D.G.sh :=
  (D.G.s0.r.dPlain, Plains.app (t := D.G.sh₂) (Plains.fst π.2)
      (D.G.s1.r.dPlain, Plains.snd (s := PQ.uL D.G.C D.G.ds₁) π.2))
/-- a position of Plain3's shape as a position of this one -/
def posB : OPos D.G.sh → OPos D.sh
  | .inl p => (D.G.s0.noPos.false p).elim
  | .inr q => match OPos.split (s := PQ.uL D.G.C D.G.ds₁) (t := D.G.sh₂) q with
    | .inl a => .inr (OPos.left a)
    | .inr (.inl p1) => (D.G.s1.noPos.false p1).elim
    | .inr (.inr b) => .inr (OPos.right (s := PQ.uL D.G.C D.G.ds₁) b)

theorem posB_left (a : OPos (PQ.uL D.G.C D.G.ds₁)) :
    D.posB (.inr (OPos.left a)) = .inr (OPos.left a) := by
  unfold posB
  simp only [OPos.split_left]

theorem posB_right (b : OPos D.shJ) :
    D.posB (.inr (OPos.right (s := PQ.uL D.G.C D.G.ds₁) (t := D.G.sh₂) (.inr b))) = .inr
        (OPos.right (s := PQ.uL D.G.C D.G.ds₁) b) := by
  unfold posB
  simp only [OPos.split_right]

theorem rho_toTr (τ : Tr D.sh) : Tr.rho (D.toTr τ) = D.toRho (Tr.rho τ) := by
  show (D.c0, Tr.rho (Tr.app (t := D.G.sh₂) (Tr.fst τ.2.2)
      ((D.G.s1.r.dOrc, D.G.s1.r.dPlain), D.c1, Tr.snd (s := PQ.uL D.G.C D.G.ds₁) τ.2.2))) =
    (D.c0, Rho.app (t := D.G.sh₂) (Rho.fst (Tr.rho τ.2.2))
        (D.c1, Rho.snd (s := PQ.uL D.G.C D.G.ds₁) (Tr.rho τ.2.2)))
  rw [Tr.rho_app, Tr.rho_fst, ← Tr.rho_snd]
  rfl

theorem plains_toTr (τ : Tr D.sh) : Tr.plains (D.toTr τ) = D.toPl (Tr.plains τ) := by
  show (D.G.s0.r.dPlain, Tr.plains (Tr.app (t := D.G.sh₂) (Tr.fst τ.2.2)
      ((D.G.s1.r.dOrc, D.G.s1.r.dPlain), D.c1, Tr.snd (s := PQ.uL D.G.C D.G.ds₁) τ.2.2))) =
    (D.G.s0.r.dPlain, Plains.app (t := D.G.sh₂) (Plains.fst (Tr.plains τ.2.2))
      (D.G.s1.r.dPlain, Plains.snd (s := PQ.uL D.G.C D.G.ds₁) (Tr.plains τ.2.2)))
  rw [Tr.plains_app, Tr.plains_fst, ← Tr.plains_snd]
  rfl

/-- the front's symbols in a transcript -/
def front (τ : Tr D.sh) : (p : D.F.r.Pos) → D.F.r.Sym p := fun p => D.F.r.rd τ.1.1 p

/-- all positions of the front -/
def frontPos : Finset (OPos D.sh) := (@Finset.univ _ D.F.pt.finPos).image Sum.inl

end BD

/-- The local protocol of one slot. -/
@[reducible] def Batch3 {X : Type} (D : BD)
    (dec : X → ((p : D.F.r.Pos) → D.F.r.Sym p) → D.F.r.Plain → PQ.View → PQ.View → PQ.View → Bool) :
    InteractiveOracleProof X (oneExternalString (2 ^ D.G.a) PQ.SgX) where
  shape := D.sh
  blinded := fun _ => true
  extReads := fun _ ρ => ((D.G.asksAt (D.toRho ρ)).filterMap (Ask.ext D.G.a)).toFinset
  reads := fun _ ρ _ => D.frontPos ∪ (((D.G.asksAt (D.toRho ρ)).filterMap D.G.own).toFinset.image
      D.posB)
  accept := fun x y τ =>
    D.G.accOn y (D.G.tr₁ (D.toTr τ)) (D.G.tr₂ (D.toTr τ)) (D.G.tr₃ (D.toTr τ))
        (dec x (D.front τ) τ.1.2)

/-- The verifier is local, for every decision. -/
theorem batch3_local {X : Type} (D : BD)
    (dec : X → ((p : D.F.r.Pos) → D.F.r.Sym p) → D.F.r.Plain → PQ.View → PQ.View → PQ.View → Bool) :
    (Batch3 D dec).IsLocal := by
  intro x y y' τ τ' hρ hp he hr
  have hf : D.front τ = D.front τ' := funext fun p =>
    hr (Sum.inl p) (Finset.mem_union_left _ (Finset.mem_image_of_mem _
        (@Finset.mem_univ _ D.F.pt.finPos p)))
  have hq : τ.1.2 = τ'.1.2 := congrArg Prod.fst hp
  show (Plain3 D.G (dec x (D.front τ) τ.1.2)).accept () y
      (D.toTr τ) = (Plain3 D.G (dec x (D.front τ') τ'.1.2)).accept () y' (D.toTr τ')
  rw [← hf, ← hq]
  refine plain3_local D.G (dec x (D.front τ) τ.1.2) () y y' (D.toTr τ) (D.toTr τ') ?_ ?_ ?_ ?_
  · rw [D.rho_toTr, D.rho_toTr, hρ]
  · rw [D.plains_toTr, D.plains_toTr, hp]
  · intro p hpm
    rw [D.rho_toTr] at hpm
    exact he p hpm
  · intro p hpm
    rw [D.rho_toTr] at hpm
    cases p with
    | inl p0 => exact (D.G.s0.noPos.false p0).elim
    | inr q =>
      have hq' := OPos.elim_split (s := PQ.uL D.G.C D.G.ds₁) (t := D.G.sh₂) q
      cases hs : OPos.split (s := PQ.uL D.G.C D.G.ds₁) (t := D.G.sh₂) q with
      | inl a =>
        rw [hs] at hq'
        obtain rfl : OPos.left a = q := hq'
        show Tr.read (Tr.app (t := D.G.sh₂) (Tr.fst τ.2.2) _) (OPos.left a) = Tr.read
            (Tr.app (t := D.G.sh₂) (Tr.fst τ'.2.2) _) (OPos.left a)
        rw [Tr.read_left_eq_iff, Tr.fst_app, Tr.fst_app, ← Tr.read_left_eq_iff]
        exact hr (Sum.inr (OPos.left a)) (Finset.mem_union_right _
            (Finset.mem_image.2 ⟨_, hpm, D.posB_left a⟩))
      | inr b =>
        rw [hs] at hq'
        obtain rfl : OPos.right (s := PQ.uL D.G.C D.G.ds₁) b = q := hq'
        cases b with
        | inl p1 => exact (D.G.s1.noPos.false p1).elim
        | inr b' =>
          show Tr.read (Tr.app (t := D.G.sh₂) (Tr.fst τ.2.2) _)
              (OPos.right (s := PQ.uL D.G.C D.G.ds₁) (Sum.inr b')) =
            Tr.read (Tr.app (t := D.G.sh₂) (Tr.fst τ'.2.2) _)
                (OPos.right (s := PQ.uL D.G.C D.G.ds₁) (Sum.inr b'))
          rw [Tr.read_right_eq_iff, Tr.snd_app, Tr.snd_app]
          show Tr.read (Tr.snd (s := PQ.uL D.G.C D.G.ds₁) τ.2.2) b' = Tr.read
              (Tr.snd (s := PQ.uL D.G.C D.G.ds₁) τ'.2.2) b'
          rw [← Tr.read_right_eq_iff]
          exact hr (Sum.inr (OPos.right (s := PQ.uL D.G.C D.G.ds₁) b'))
            (Finset.mem_union_right _ (Finset.mem_image.2 ⟨_, hpm, D.posB_right b'⟩))

/-! ## The annotation -/

/-- written rounds, all local, before what follows -/
def annLo (C : PQ.CK) (t : Shape) (At : RoundSplits t) : (ds : List PQ.RD) → RoundSplits (PQ.uL C ds ++ t)
  | [] => At
  | d :: ds => (RAnn.allLocal (PQ.roundS C d).up, annLo C t At ds)

/-- written rounds, all shared: only the shared part is sent -/
def annSh (C : PQ.CK) (t : Shape) (At : RoundSplits t) : (ds : List PQ.RD) → RoundSplits (PQ.uL C ds ++ t)
  | [] => At
  | d :: ds => (RAnn.ofShared .sh (PQ.roundS C d).up, annSh C t At ds)

theorem annLo_coherent (C : PQ.CK) (t : Shape) (At : RoundSplits t) (h : At.Coherent) :
    ∀ ds : List PQ.RD, (annLo C t At ds).Coherent
  | [] => h
  | _ :: ds => ⟨RAnn.ofSlot_coherent _ _, annLo_coherent C t At h ds⟩

theorem annSh_coherent (C : PQ.CK) (t : Shape) (At : RoundSplits t) (h : At.Coherent) :
    ∀ ds : List PQ.RD, (annSh C t At ds).Coherent
  | [] => h
  | _ :: ds => ⟨RAnn.ofShared_coherent _ _, annSh_coherent C t At h ds⟩

/-- the maker of local annotations is the library's RoundSplits.app at RoundSplits.allLocal -/
theorem annLo_eq_app (C : PQ.CK) (t : Shape) (At : RoundSplits t) :
    ∀ ds : List PQ.RD, annLo C t At ds = RoundSplits.app (RoundSplits.allLocal (PQ.uL C ds)) At
  | [] => rfl
  | d :: ds => by
    show (RAnn.allLocal (PQ.roundS C d).up, annLo C t At ds) =
        (RAnn.allLocal (PQ.roundS C d).up, RoundSplits.app (RoundSplits.allLocal (PQ.uL C ds)) At)
    rw [annLo_eq_app C t At ds]

/-- the maker of shared annotations is the library's RoundSplits.app at RoundSplits.const (RAnn.ofShared .sh) -/
theorem annSh_eq_app (C : PQ.CK) (t : Shape) (At : RoundSplits t) :
    ∀ ds : List PQ.RD, annSh C t At ds = RoundSplits.app (RoundSplits.const (RAnn.ofShared .sh) (PQ.uL C ds)) At
  | [] => rfl
  | d :: ds => by
    show (RAnn.ofShared .sh (PQ.roundS C d).up, annSh C t At ds) =
      (RAnn.ofShared .sh (PQ.roundS C d).up, RoundSplits.app
          (RoundSplits.const (RAnn.ofShared .sh) (PQ.uL C ds)) At)
    rw [annSh_eq_app C t At ds]

namespace BD
variable (D : BD)

/-- the local seam behind the shared block, and the third stretch -/
def ann₃ : RoundSplits D.G.sh₃ := RoundSplits.allLocal D.G.sh₃

/-- THE JOINING ROUND; the shared stretch; what follows -/
def annJ : RoundSplits D.shJ := (D.aJ, annSh D.G.C D.G.sh₃ D.ann₃ D.G.ds₂)

/-- The annotation. -/
def ann : RoundSplits D.sh := (RAnn.allLocal D.F.r, annLo D.G.C D.shJ D.annJ D.G.ds₁)

theorem annJ_coherent (hJ : D.aJ.Coherent) : D.annJ.Coherent :=
  And.intro hJ (annSh_coherent D.G.C D.G.sh₃ D.ann₃ (BatchOne.BAnn.allLocal_coherent _) D.G.ds₂)

theorem ann_coherent (hJ : D.aJ.Coherent) : D.ann.Coherent :=
  And.intro (RAnn.ofSlot_coherent _ _) (annLo_coherent D.G.C D.shJ D.annJ
      (D.annJ_coherent hJ) D.G.ds₁)

end BD

theorem annLo_localTo (C : PQ.CK) (t : Shape) (At : RoundSplits t) :
    ∀ (ds : List PQ.RD) (n : ℕ), n < ds.length → RoundSplits.LocalTo n (PQ.uL C ds ++ t) (annLo C t At ds)
  | _ :: _, 0, _ => rfl
  | _ :: ds, n + 1, h => ⟨rfl, annLo_localTo C t At ds n (Nat.lt_of_succ_lt_succ h)⟩

/-- the front and the first stretch are local: up to every round number n ≤ the first stretch's
length -/
theorem BD.ann_localTo (D : BD) : ∀ n, n ≤ D.G.ds₁.length → RoundSplits.LocalTo n D.sh D.ann
  | 0, _ => rfl
  | n + 1, h => ⟨rfl, annLo_localTo D.G.C D.shJ D.annJ D.G.ds₁ n h⟩

/-- The batch protocol. -/
@[reducible] def BatchP {X : Type} (D : BD)
    (dec : X → ((p : D.F.r.Pos) → D.F.r.Sym p) → D.F.r.Plain → PQ.View → PQ.View → PQ.View → Bool) :
    BatchInteractiveOracleProof X (oneExternalString (2 ^ D.G.a) PQ.SgX) := ⟨Batch3 D dec, D.ann⟩

end TypedOracleCompiler.Slice
