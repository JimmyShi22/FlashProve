-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Run/ReqClimb.lean: THE REQUEST TREE: THE PORT's CLIMB IN THE BINDING TREE AGAINST THE
TYPED VERIFIER's CHECK reqCheck. A piece of "the tie at H_b" for a proof file (LinkF).
The compiler under OnBytes/TypedOracleCompiler/ is the one that `innerCompiledVerifier` is made with; it builds on
definitions of Compile/.
WHY. A part's checker is
"the typing (a twin of the port's strict reader), then the typed verifier under the family that the
page makes of the hash"; owed: the port's yes gives that run's yes. HERE: the part of it that
concerns the request tree. THE PORT's SIDE: ChecksWithHashAsArgument/ProofWith.lean: readPlaceW, climbW (the port's
text with what hashes as arguments F : HashFns). THE TYPED SIDE: the road's reqCheck: the leaf's
input is the slot value with the string rsalt behind it.
  saltAt s b i, sibsAt b j n     the salt (s.saltBytes bytes behind the place's word) and the n
                                 siblings of 32 bytes from byte j on, AS SLICES OF THE FILE: what a
                                 typing lays into π.rsalt and π.path
  foldW F cfg sibs x p           the fold of F.vertB cfg from x along the siblings, by the low bits
                                 of p: the port's own "if p % 2 == 1 then vertB cfg sib x else vertB
                                 cfg x sib"
  climbW_some                    climbW … = some r → r = (that fold at sibsAt, the byte behind
                                 them), and each sibling has 32 bytes
  PlaceRead, readPlaceW_some (i) WHAT A YES OF readPlaceW SAYS, FIELD BY FIELD: the shape is
  admitted; the word w at byte i; w < 2 ^ logLeaves; the salt's and the siblings' bytes are within
  the file; p.place = w; p.root = the fold from F.leafB …; p.places; p.next
  ofFn_bytesToDig                32 bytes as a digest, as bits, are the bytes' bits
  RowLaws g F depth sB cfg closing   THE TWO "ROW LAWS", AS HYPOTHESES (no family, no page is
                                     named): AT place < 2 ^ depth AND A SALT OF sB BYTES: g at rleaf
                                     (bits closing ++ (bits salt ++ bits (u64n place))) is F.leafB
                                     depth place cfg closing salt as a digest [the inputs that
                                     pR173, a code in a file of this project that is not in this
                                     library, writes,
                                 and no other: asked at all numbers and salts no family behind a
                                 page could have the law]; g at rnode (l, r), l and r of 256 bits,
                                 is F.vertB cfg (l's bytes) (r's bytes) as a digest; and F's two
                                 functions give 32 bytes
  climbF_foldW               THE SIDES, WALKED: the library's pure climb (climbF_cons: "if j % 2 = 0
                             then hN c s else hN s c") at the typed vertex function IS the port's
                             fold: at an even place the sibling is the right child, at an odd one
                             the left, in both
  reqCheck_fold              (ii) under the row laws: (reqCheck depth (the fold as a digest) place
                             (the siblings as digests) (closing as a digest) (bits salt ++ bits
                             (u64n place))).det g = true
  reqCheck_of_readPlaceW     BOTH TOGETHER: readPlaceW F s cfg closing b i = some p → (reqCheck
                             s.logLeaves p.root p.place (sibsAt …) closing (bits (saltAt …) ++ bits
                             (u64n p.place))).det g = true
WHAT IS NOT SAID. THAT ANY FAMILY HAS THE ROW LAWS (the page's: pR173 and pNode178 are codes; no
family asks the oracle at their strings yet). That closing is the slot value that the typed chain
reaches ((G)'s answer: the seam's). That p.root is what (F4) holds (the seam's). The converse (a
typed yes gives the port's) is not claimed and not wanted. Values under oracle FUNCTIONS (.det g):
the order of asking does not enter: in the file the tree is climbed BEFORE the shared chain, in the
typed run at the end. The typed verifier does not hold the word inside rsalt against π.slot: here
they are equal by construction.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.ChecksWithHashAsArgument.ProofWith
import OnBytes.TypedOracleCompiler.Run.VerifyDetProofs
import Run.Toy1TieTree

set_option autoImplicit false

namespace TypedOracleCompiler.Run
open TypedOracleCompiler.Iop Rom _root_.Compile TypedOracleCompiler.Compile.Batch
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run
open OnBytes.TwoPort (HashFns climbW readPlaceW)
open OnBytes.Proof (Place bindingOk)

/-! ## (i) The port's side -/

/-- the leaf's salt: the bytes behind the place's word -/
def saltAt (s : OnBytes.Params.LinBindingShape) (b : ByteArray) (i : ℕ) : ByteArray :=
  b.extract (i + 8) (i + 8 + s.saltBytes)

/-- n siblings of 32 bytes from byte j on, the leaf's sibling first -/
def sibsAt (b : ByteArray) : ℕ → ℕ → List ByteArray
  | _, 0 => []
  | j, n + 1 => b.extract j (j + 32) :: sibsAt b (j + 32) n

theorem length_sibsAt (b : ByteArray) : ∀ (n j : ℕ), (sibsAt b j n).length = n
  | 0, _ => rfl
  | n + 1, j => congrArg (· + 1) (length_sibsAt b n (j + 32))

/-- the port's fold: x is the value of a vertex, p its place in its level -/
def foldW (F : HashFns) (cfg : ByteArray) : List ByteArray → ByteArray → ℕ → ByteArray
  | [], x, _ => x
  | sib :: l, x, p => foldW F cfg l (if p % 2 == 1 then F.vertB cfg sib x else F.vertB cfg x sib)
      (p / 2)

theorem slice_some {b : ByteArray} {i n : ℕ} {x : ByteArray} (h : _root_.Fmt.slice b i n = some x) :
    x = b.extract i (i + n) ∧ i + n ≤ b.size := by
  unfold _root_.Fmt.slice at h
  split at h
  · rename_i hle
    exact ⟨(Option.some.inj h).symm, hle⟩
  · cases h

theorem size_extract_of_le {b : ByteArray} {i n : ℕ} (h : i + n ≤ b.size) :
    (b.extract i (i + n)).size = n := by
  rw [ByteArray.size_extract]
  omega

theorem climbW_some (F : HashFns) (cfg b : ByteArray) :
    ∀ (levels : ℕ) (x : ByteArray) (p i : ℕ) (r : ByteArray × ℕ),
        climbW F cfg b levels x p i = some r →
      r = (foldW F cfg (sibsAt b i levels) x p, i + 32 * levels) ∧ i + 32 * levels ≤ max i b.size ∧
        ∀ sib ∈ sibsAt b i levels, sib.size = 32
  | 0, x, p, i, r, h => by
      have h' : some (x, i) = some r := h
      cases Option.some.inj h'
      exact ⟨rfl, Nat.le_max_left _ _, fun _ hs => by cases hs⟩
  | levels + 1, x, p, i, r, h => by
      unfold climbW at h
      cases hs : _root_.Fmt.slice b i 32 with
      | none => rw [hs] at h; cases h
      | some sib =>
        rw [hs] at h
        obtain ⟨rfl, hle⟩ := slice_some hs
        obtain ⟨h1, h2, h3⟩ := climbW_some F cfg b levels _ (p / 2) (i + 32) r h
        refine ⟨?_, ?_, ?_⟩
        · rw [h1]
          exact Prod.ext rfl (show i + 32 + 32 * levels = i + 32 * (levels + 1) by omega)
        · omega
        · intro s' hs'
          rcases List.mem_cons.1 hs' with rfl | hs'
          · exact size_extract_of_le hle
          · exact h3 _ hs'

/-- What a yes of the place's reader says. -/
structure PlaceRead (F : HashFns) (s : OnBytes.Params.LinBindingShape) (cfg closing b : ByteArray)
    (i : ℕ) (p : Place)
    (w : UInt64) : Prop where
  /-- the format admits the shape -/
  shape : bindingOk s = true
  /-- the place's word stands at byte i -/
  word : _root_.Fmt.rdWord b i = some (w, i + 8)
  /-- it is the number of a leaf -/
  lt : w.toNat < 2 ^ s.logLeaves
  /-- the salt's bytes are within the file -/
  salt : _root_.Fmt.slice b (i + 8) s.saltBytes = some (saltAt s b i)
  saltSize : (saltAt s b i).size = s.saltBytes
  /-- each sibling has 32 bytes -/
  sibs : ∀ sib ∈ sibsAt b (i + 8 + s.saltBytes) s.logLeaves, sib.size = 32
  place : p.place = w.toNat
  /-- the root: the fold from the leaf -/
  root : p.root = foldW F cfg (sibsAt b (i + 8 + s.saltBytes) s.logLeaves)
    (F.leafB s.logLeaves w.toNat cfg closing (saltAt s b i)) w.toNat
  places : p.places = 2 ^ s.logLeaves
  next : p.next = i + 8 + s.saltBytes + 32 * s.logLeaves

theorem readPlaceW_some {F : HashFns} {s : OnBytes.Params.LinBindingShape}
    {cfg closing b : ByteArray} {i : ℕ} {p : Place}
    (h : readPlaceW F s cfg closing b i = some p) : ∃ w, PlaceRead F s cfg closing b i p w := by
  unfold readPlaceW at h
  cases hb : bindingOk s with
  | false => rw [hb] at h; cases h
  | true =>
    rw [hb] at h
    cases hw : _root_.Fmt.rdWord b i with
    | none => rw [hw] at h; cases h
    | some wi =>
      obtain ⟨w, i1⟩ := wi
      rw [hw] at h
      have hi1 : i1 = i + 8 := by
        unfold _root_.Fmt.rdWord at hw
        split at hw
        · exact (congrArg Prod.snd (Option.some.inj hw)).symm
        · cases hw
      subst hi1
      by_cases hlt : 2 ^ s.logLeaves ≤ w.toNat
      · simp only [Bool.not_true, Bool.false_eq_true, if_false, if_pos hlt] at h
        cases h
      · simp only [Bool.not_true, Bool.false_eq_true, if_false, if_neg hlt] at h
        cases hs : _root_.Fmt.slice b (i + 8) s.saltBytes with
        | none => rw [hs] at h; cases h
        | some salt =>
          rw [hs] at h
          obtain ⟨rfl, hle⟩ := slice_some hs
          obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.1 h
          obtain ⟨h1, -, h3⟩ := climbW_some F cfg b _ _ _ _ x hx
          exact ⟨w, hb, hw, Nat.lt_of_not_le hlt, hs, size_extract_of_le hle, h3, rfl,
            congrArg Prod.fst h1, rfl, congrArg Prod.snd h1⟩

/-! ## (ii) The typed side -/

/-- 32 bytes as a digest, as bits, are the bytes' bits -/
theorem ofFn_bytesToDig (x : ByteArray) (h : x.size = 32) :
    List.ofFn (bytesToDig x) = bytesToBits x := by
  have e : bitsToBytes (List.ofFn (bytesToDig x)) = x := _root_.Run.TieTree.dig_bytes x h
  have w : whole (List.ofFn (bytesToDig x)) = true := by
    unfold whole
    rw [List.length_ofFn]
    rfl
  rw [← bytesToBits_bitsToBytes _ w, e]

section
variable {I X : Type} {K : ℕ} {L : BatchProtocolWithLeafBody I X}

/-- The two row laws, and that the two functions give 32 bytes. -/
structure RowLaws (g : Fam (TypedOracleCompiler.Compile.Batch.typedOracleFamily 256 K L)) (F : HashFns) (depth sB : ℕ)
    (cfg closing : ByteArray) : Prop where
  /-- the typed leaf: the slot value, the salt, the place's word: AT THE NUMBER OF A LEAF AND A SALT
  OF sB BYTES ALONE (a code such as pR173 writes no other input; and the word of a number from 2 ^
  64 on is another number's) -/
  leaf : ∀ (place : ℕ) (salt : ByteArray), place < 2 ^ depth → salt.size = sB →
    (g TypedOracleCompiler.Compile.Batch.OracleName.rleaf
      (bytesToBits closing ++ (bytesToBits salt ++ bytesToBits (_root_.Fmt.u64n place)) : Bits) :
          Dig 256) =
      bytesToDig (F.leafB depth place cfg closing salt)
  /-- the typed vertex -/
  node : ∀ l r : Bits, l.length = 256 → r.length = 256 →
    (g TypedOracleCompiler.Compile.Batch.OracleName.rnode ((l, r) : Bits × Bits) : Dig 256) =
      bytesToDig (F.vertB cfg (bitsToBytes l) (bitsToBytes r))
  leafSize : ∀ (place : ℕ) (salt : ByteArray), place < 2 ^ depth → salt.size = sB →
    (F.leafB depth place cfg closing salt).size = 32
  nodeSize : ∀ l r : ByteArray, (F.vertB cfg l r).size = 32

variable {g : Fam (TypedOracleCompiler.Compile.Batch.typedOracleFamily 256 K L)} {F : HashFns} {depth sB : ℕ}
    {cfg closing : ByteArray}

theorem RowLaws.rnodeF (R : RowLaws g F depth sB cfg closing) (a c : ByteArray) (ha : a.size = 32)
    (hc : c.size = 32) :
    rnodeF g (bytesToDig a) (bytesToDig c) = bytesToDig (F.vertB cfg a c) := by
  have e := R.node (List.ofFn (bytesToDig a)) (List.ofFn (bytesToDig c)) List.length_ofFn
      List.length_ofFn
  have ea : bitsToBytes (List.ofFn (bytesToDig a)) = a := _root_.Run.TieTree.dig_bytes a ha
  have ec : bitsToBytes (List.ofFn (bytesToDig c)) = c := _root_.Run.TieTree.dig_bytes c hc
  rw [ea, ec] at e
  exact e

/-- The sides: the library's pure climb at the typed vertex function is the port's fold. -/
theorem climbF_foldW (R : RowLaws g F depth sB cfg closing) :
    ∀ (sibs : List ByteArray) (x : ByteArray) (p : ℕ), x.size = 32 → (∀ sib ∈ sibs, sib.size = 32) →
      climbF (rnodeF g) (sibs.map bytesToDig) p (bytesToDig x) = bytesToDig (foldW F cfg sibs x p)
  | [], _, _, _, _ => rfl
  | sib :: l, x, p, hx, hs => by
      have hsib : sib.size = 32 := hs sib List.mem_cons_self
      have hl : ∀ s' ∈ l, s'.size = 32 := fun s' h => hs s' (List.mem_cons_of_mem _ h)
      rw [List.map_cons, climbF_cons]
      show _ = bytesToDig (foldW F cfg l (if p % 2 == 1 then F.vertB cfg sib x else F.vertB cfg
          x sib) (p / 2))
      by_cases hp : p % 2 = 0
      · have e : (p % 2 == 1) = false := by rw [hp]; rfl
        rw [if_pos hp, e, R.rnodeF x sib hx hsib]
        exact climbF_foldW R l _ _ (R.nodeSize _ _) hl
      · have e : (p % 2 == 1) = true := by
          have : p % 2 = 1 := by omega
          rw [this]; rfl
        rw [if_neg hp, e, R.rnodeF sib x hsib hx]
        exact climbF_foldW R l _ _ (R.nodeSize _ _) hl

/-- The typed check accepts the port's fold. -/
theorem reqCheck_fold (R : RowLaws g F depth sB cfg closing) (hc : closing.size = 32) (place : ℕ)
    (hp : place < 2 ^ depth)
    (salt : ByteArray) (hsalt : salt.size = sB) (sibs : List ByteArray) (hlen : sibs.length = depth)
        (hs : ∀ sib ∈ sibs, sib.size = 32) :
    (reqCheck (L := L) (K := K) depth
      (bytesToDig (foldW F cfg sibs (F.leafB depth place cfg closing salt) place)) place
          (sibs.map bytesToDig)
      (bytesToDig closing) (bytesToBits salt ++ bytesToBits (_root_.Fmt.u64n place))).det
          g = true := by
  rw [reqCheck_det]
  unfold reqCheckF
  rw [if_pos ⟨by rw [List.length_map]; exact hlen, hp⟩, ofFn_bytesToDig closing hc, R.leaf place salt hp hsalt]
  exact decide_eq_true (climbF_foldW R sibs _ place (R.leafSize _ _ hp hsalt) hs)

/-- The port's yes at the place gives the typed check's yes, at the string that a typing makes of
the file's slices. -/
theorem reqCheck_of_readPlaceW {s : OnBytes.Params.LinBindingShape} {b : ByteArray}
    {i : ℕ} {p : Place}
    (R : RowLaws g F s.logLeaves s.saltBytes cfg closing) (hc : closing.size = 32)
    (h : readPlaceW F s cfg closing b i = some p) :
    (reqCheck (L := L) (K := K) s.logLeaves (bytesToDig p.root) p.place
      ((sibsAt b (i + 8 + s.saltBytes) s.logLeaves).map bytesToDig) (bytesToDig closing)
      (bytesToBits (saltAt s b i) ++ bytesToBits (_root_.Fmt.u64n p.place))).det g = true := by
  obtain ⟨w, P⟩ := readPlaceW_some h
  rw [P.root, P.place]
  exact reqCheck_fold R hc w.toNat P.lt _ P.saltSize _ (length_sibsAt b _ _) P.sibs

end

end TypedOracleCompiler.Run
