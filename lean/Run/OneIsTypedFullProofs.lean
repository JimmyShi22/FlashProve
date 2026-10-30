-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/OneIsTypedFullProofs.lean: the proofs of the three statements of Run/OneIsTypedFull.lean. Many
statements of this library are written twice: a definition in the namespace `Spec` states a
proposition, and a theorem of the same name outside that namespace proves it (lean/GLOSSARY.md).

`oneW_is_typed`, `oneW_pull`, `oneW_ck`: the run over the single oracle as the run at the typed
oracle functions (statements and hypotheses: Run/OneIsTypedFull.lean). Limits: the head of
Run/OneIsTypedFull.lean.

The method of proof is that of Run/OneIsTyped.lean and Run/OneIsTypedTop.lean, whose generic parts
are used as they are. The flag (in the doc comments of `askP_flag`, `askP_allW`, `askedQW`) is the
wiring's flag for pruned openings (`prJ`, Iop/BatchWire.lean); it is false at the wiring with whole
paths.

Main names (what this file adds):
  `askP_flag`, `askP_allW`: the test on the chain's queries reads of a round's wiring only whether
    it has a tree.
  `parse_factsW`: for `ok S = true`, the whole-path parser's strings have a first salt of 256 bits
    and nonces below 2^64.
-/
/- Limits: that a proof file is accepted or refused is no theorem of this library. It is the outcome
   of a `#guard` line, or of an evaluation outside the library, such as a test by Lean's evaluator,
   which leaves no declaration. So nothing that is checked of declarations is checked of such an
   evaluation. No clause of a soundness theorem of Fmt/ and Run/ speaks of a run. -/
import Run.OneIsTypedFull

set_option autoImplicit false

namespace Run.PQ
open Rom Iop Compile Compile.Batch Run.Thin Run.Twin
open _root_.Fmt (Item RoundOut ChainOut Plan St)

section
variable (S : _root_.Fmt.Spec) (C : CK) (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k)
  (dec : View → Bool) (h : OKQ S = true)

/-- The test on the chain's queries does not see the flag. -/
theorem askP_flag (g : Fam (spec 256 (K + 1) (LbS C (rds S) dec)))
    (Pq : FbIn 256 (LbS C (rds S) dec) .onl → Bool) (cm : Dig 256) (salt : Bits) :
    ∀ (ds : List RD) (embP : PlainPart (uL C ds) (allLo (SL C ds)) → PBQ S C dec) (i : ℕ) (v : Bits)
        (rts : List (Dig 256)) (pls : Plains (uL C ds)),
      askP (lam := 256) (K := K + 1) (fun _ => LbS C (rds S) dec) g id none .onl Pq [cm]
          (some () : Option Unit) salt (SL C ds) (allLo (SL C ds)) (wiresSLF C K chal ds)
          embP i (.loc v) rts pls =
        askP (lam := 256) (K := K + 1) (fun _ => LbS C (rds S) dec) g id none .onl Pq
          [cm] (some () : Option Unit) salt (SL C ds) (allLo (SL C ds))
          (wiresSL C K chal ds) embP i (.loc v) rts pls
  | [], _, _, _, _, _ => rfl
  | d :: ds, embP, i, v, rts, (pl, pls) => by
    refine (askP_lo (fun _ => LbS C (rds S) dec) g .onl Pq [cm] salt (roundS C d) (SL C ds)
      (allLo (SL C ds)) (wireSF C K chal d) (wiresSLF C K chal ds) embP i v rts pl pls).trans ?_
    refine Eq.trans ?_
      (askP_lo (fun _ => LbS C (rds S) dec) g .onl Pq [cm] salt (roundS C d) (SL C ds)
        (allLo (SL C ds)) (wireS C K chal d) (wiresSL C K chal ds) embP i v rts pl pls).symm
    rw [show (wireSF C K chal d).hasJ = (wireS C K chal d).hasJ from rfl]
    cases takeRt (wireS C K chal d).hasJ rts with
    | none => rfl
    | some x =>
      obtain ⟨rt, rts'⟩ := x
      show (Pq _ && _) = (Pq _ && _)
      rw [askP_flag g Pq cm salt ds (fun z => embP (.inr z)) (i + 1) _ rts' pls]

/-- Under the hypotheses of `askP_all` (Run/OneIsTypedChain.lean): every chain query that the
verifier forms fits, at every family: at the wiring without the flag. -/
theorem askP_allW (g : Fam (spec 256 (K + 1) (LbS C (rds S) dec))) (cm : Dig 256) (salt : Bits)
    (hK : K + 1 < 2 ^ 48) (hkind : ∀ i, (chainQ S C dec).kind i < 256)
    (hwork : ∀ i, (chainQ S C dec).work i < 256) (hs : salt.length = 256)
    (hst : S.statement.size < 2 ^ 64) (hr : RootsFit (rds S)) (hlen : (rds S).length < 2 ^ 64)
    (rts : List (Dig 256)) (pls : Plains (uL C (rds S))) (hn : noncesOK C (rds S) pls) :
    askP (lam := 256) (K := K + 1) (fun _ => LbS C (rds S) dec) g id none .onl (fitFb S C K dec h)
        [cm] (some () : Option Unit) salt (PSof C (rds S) dec).S (PSof C (rds S) dec).ann
        (wqSF C K chal (rds S) dec).sh (embPS C (rds S) dec) 0 .first rts ((), pls) = true := by
  have h0 := askP_all S C K chal dec h g cm salt hK hkind hwork hs hst hr hlen rts pls hn
  have h1 : (fitFb S C K dec h
          (⟨0, .f1 [cm] (some ()) salt, none,
            embPS C (rds S) dec (.inl (.inr ()))⟩ : FbIn 256 (LfQ S C dec ()) .onl) &&
        askP (lam := 256) (K := K + 1) (fun _ => LbS C (rds S) dec) g id none .onl
          (fitFb S C K dec h) [cm] (some () : Option Unit) salt (SL C (rds S))
          (allLo (SL C (rds S))) (wiresSL C K chal (rds S))
          (fun z => embPS C (rds S) dec (.inr z)) 1
          (.loc (List.ofFn
              (g (OracleName.fb .onl)
                (⟨0, .f1 [cm] (some ()) salt,
                  none,
                  embPS C (rds S) dec
                    (.inl (.inr ()))⟩ : FbIn 256 (LbS C (rds S) dec) .onl) : (Fin (K + 1) → Dig 256) × Dig 256).2))
          rts pls) = true := h0
  show (fitFb S C K dec h
        (⟨0, .f1 [cm] (some ()) salt, none,
          embPS C (rds S) dec (.inl (.inr ()))⟩ : FbIn 256 (LfQ S C dec ()) .onl) &&
      askP (lam := 256) (K := K + 1) (fun _ => LbS C (rds S) dec) g id none .onl (fitFb S C K dec h)
        [cm] (some () : Option Unit) salt (SL C (rds S)) (allLo (SL C (rds S)))
        (wiresSLF C K chal (rds S)) (fun z => embPS C (rds S) dec (.inr z)) 1
        (.loc (List.ofFn
            (g (OracleName.fb .onl)
              (⟨0, .f1 [cm] (some ()) salt,
                none,
                embPS C (rds S) dec
                  (.inl (.inr ()))⟩ : FbIn 256 (LbS C (rds S) dec) .onl) : (Fin (K + 1) → Dig 256) × Dig 256).2))
        rts pls) = true
  rw [askP_flag]
  exact h1

/-- The test on an argument string, at the wiring without the flag. -/
def askedQW (cm : Dig 256) (π : OneProtocolProof 256 (PSof C (rds S) dec).up) : Bool :=
  askedP (lam := 256) (K := K + 1) (fun _ => LbS C (rds S) dec) (gQ S C dec (K + 1) h) id none
    (256 + 8 * S.plan.salt) 256 .onl (fitFb S C K dec h) (fitLeaf S C K dec h) (PSof C (rds S) dec)
    (wqSF C K chal (rds S) dec) (fun p a => some (.inr ⟨Tag.onl, ⟨p, a⟩⟩)) (embPS C (rds S) dec)
    some (fun s => some (.inl s)) 0 [cm] () π

/-- For `OKQ S = true` (`h`): where that test holds (`ha`), the verifier over the single oracle is
the verifier at the typed oracle functions. -/
theorem one_askedW (cm : Dig 256) (π : OneProtocolProof 256 (PSof C (rds S) dec).up)
    (ha : askedQW S C K chal dec h cm π = true) :
    V1W S C K chal dec h cm π = VPFC S C K chal dec cm π := by
  have F := pageQ_fit S C dec (K + 1) (Nat.succ_pos K) h
  unfold V1W VPFC
  rw [verifyPR_eq, verifyPB_eq, verifyPB_eq, famK_eq, famP_eq]
  have hw : FrontBlind (lam := 256) (K := K + 1) (PSof C (rds S) dec).S
      (PSof C (rds S) dec).ann (wqSF C K chal (rds S) dec).sh :=
    fun _ _ => Subsingleton.elim _ _
  refine verifyP_asked (fun _ => LbS C (rds S) dec) _ _ id none _ 256 .onl
    (fitFb S C K dec h) (fitLeaf S C K dec h) ?_ ?_ ?_ (PSof C (rds S) dec)
    (wqSF C K chal (rds S) dec) hw _ _ _ _ 0 [cm] () π ha
  · intro q hq
    rw [gQ_eq]
    exact allBlocks_fb _ _ F q (fitFb_fits S C K dec h q hq)
  · intro q hq
    rw [gQ_eq]
    exact allBlocks_leaf _ _ F q hq
  · intro a b
    unfold Thin.nodeP
    rw [gQ_eq]
    refine allBlocks_node _ _ F _ ?_
    rw [pNode_put _ _ _ List.length_ofFn List.length_ofFn]
    rfl

/-- Under `h` (`OKQ S = true`) and `FitsS S K` (`F`): on a string with a first salt of 256 bits
(`hs`) and nonces below 2^64 (`hn`) the verifier asks nothing off the plan (`askedQW .. = true`). -/
theorem asked_ofW (F : FitsS S K) (cm : Dig 256) (π : OneProtocolProof 256 (PSof C (rds S) dec).up)
    (hs : π.salt.length = 256) (hn : noncesOK C (rds S) π.plains.2) :
    askedQW S C K chal dec h cm π = true := by
  unfold askedQW askedP
  rw [Bool.and_eq_true]
  refine ⟨askP_allW S C K chal dec h _ cm π.salt F.k48 (kindQ_lt S C dec) (workQ_lt S C dec F.work)
      hs F.stm F.roots F.len π.roots π.plains.2 hn,
    ?_⟩
  cases hc : chainP (lam := 256) (K := K + 1) (fun _ => LbS C (rds S) dec)
      (gQ S C dec (K + 1) h) id none .onl [cm] (some () : Option Unit) π.salt π.rtreq
      (PSof C (rds S) dec).S (PSof C (rds S) dec).ann (wqSF C K chal (rds S) dec).sh
      (embPS C (rds S) dec) 0 .first π.roots π.plains with
  | none => rfl
  | some z =>
    obtain ⟨ρ, rts, ph⟩ := z
    show (!strictP (256 + 8 * S.plan.salt) 256 (PSof C (rds S) dec)
          (wqSF C K chal (rds S) dec) 0 () π ρ rts ph || _) = true
    by_cases hst : strictP (256 + 8 * S.plan.salt) 256 (PSof C (rds S) dec)
        (wqSF C K chal (rds S) dec) 0 () π ρ rts ph = true
    · rw [hst, Bool.not_true, Bool.false_or, Bool.and_eq_true]
      refine ⟨?_, ?_⟩
      · have := chainP_local (fun _ => LbS C (rds S) dec) (gQ S C dec (K + 1) h) id none .onl [cm]
          (some () : Option Unit) π.salt π.rtreq (SOf C (rds S)) (wqSF C K chal (rds S) dec).sh
          (embPS C (rds S) dec) 0 .first π.roots π.plains (ρ, rts, ph) rfl hc
        rw [show ph.slotVal = none from this]
        rfl
      · cases hf : forestsOfP (fun _ => LbS C (rds S) dec) (PSof C (rds S) dec)
            (wqSF C K chal (rds S) dec) (fun p a => some (.inr ⟨Tag.onl, ⟨p, a⟩⟩))
            (fun s => some (.inl s)) [cm] () π ρ rts with
        | none => rfl
        | some Fs =>
          show ((flatP (fun _ => LbS C (rds S) dec) Fs).all fun c => fitLeaf S C K dec h c.inp) =
            true
          rw [List.all_eq_true]
          intro c hcm
          obtain ⟨p, a, salt, e1, e2⟩ :=
            forestsOfP_inp (fun _ => LbS C (rds S) dec) (256 + 8 * S.plan.salt)
              256 (PSof C (rds S) dec) (wqSF C K chal (rds S) dec) _ _ 0 [cm] ()
              π ρ rts ph hst rfl Fs hf c hcm
          rw [e1]
          exact leaf_fits S C K dec h S.firstTree F.num F.small F.salt p a salt e2
    · rw [Bool.not_eq_true] at hst
      rw [hst]
      rfl

end

/-! ### What the cut of a chain in a file returns, for any reader of openings -/

section
variable (h : HId)

theorem cutStep_nonce (ops : OpsW Id) (P : Plan) (run : Option ByteArray) (b : ByteArray)
    (s s' : St) (r : _root_.Fmt.Round) (e : cutStep (m := Id) h ops P run b s r = some s') :
    ∃ ro : RoundOut, s'.out = s.out.push ro ∧ ro.nonce < 2 ^ 64 := by
  unfold cutStep at e
  split at e
  · cases e
  · rename_i msg hmsg
    split at e
    · cases e
    · rename_i vals hvals
      split at e
      · cases e
      · rename_i nonce i1 hnon
        simp only [idb] at e
        cases hq : laxQueryW (m := Id) h s.chain msg r.kind r.entry.work nonce
            ((_root_.Fmt.wordsAtMost r.entry r.kind + 3) / 4) with
        | none => rw [hq] at e; cases e
        | some cv =>
          rw [hq] at e
          dsimp only at e
          obtain ⟨hk, -, -⟩ := laxQuery_some h _ _ _ _ _ _ cv.1 cv.2 hq
          split at e
          · cases e
          · rename_i u i2 hlist
            split at e
            · cases e
            · rename_i cols i3 hops
              cases e
              refine ⟨⟨msg, vals, nonce, _, _, cols⟩, rfl, ?_⟩
              simp only [_root_.Fmt.askOK, Bool.and_eq_true, decide_eq_true_eq] at hk
              exact hk.1.1.2

theorem cutFold_nonce (ops : OpsW Id) (P : Plan) (run : Option ByteArray) (b : ByteArray) :
    ∀ (rs : List _root_.Fmt.Round) (s s' : St), cutFold (m := Id) h ops P run b rs s = some s' →
      (∀ ro ∈ s.out.toList, ro.nonce < 2 ^ 64) → ∀ ro ∈ s'.out.toList, ro.nonce < 2 ^ 64
  | [], s, s', e, hs => by
      obtain rfl := Option.some.inj e
      exact hs
  | r :: rs, s, s', e, hs => by
      simp only [cutFold, idb] at e
      cases hc : cutStep (m := Id) h ops P run b s r with
      | none => rw [hc] at e; cases e
      | some s1 =>
        rw [hc] at e
        dsimp only at e
        obtain ⟨ro, h1, h2⟩ := cutStep_nonce h ops P run b s s1 r hc
        refine cutFold_nonce ops P run b rs s1 s' e fun ro' hr => ?_
        rw [h1, Array.toList_push, List.mem_append, List.mem_singleton] at hr
        rcases hr with hr | rfl
        · exact hs ro' hr
        · exact h2

theorem cutChain_facts (ops : ByteArray → OpsW Id) (S : _root_.Fmt.Spec) (hr : S.rand = .inFile)
    (b : ByteArray) (i : ℕ) (o : ChainOut) (j : ℕ)
    (e : cutChain (m := Id) h ops S b i = some (o, j)) :
    (∃ x : ByteArray, o.run = some (h 172 0 S.label _root_.Fmt.zero32 x)) ∧
    ∀ ro ∈ o.rounds.toList, ro.nonce < 2 ^ 64 := by
  unfold cutChain at e
  rw [hr] at e
  split at e
  · cases e
  · dsimp only at e
    split at e
    · cases e
    · rename_i x i0 hx
      simp only [_root_.Fmt.paramsDigestW, idb] at e
      split at e
      · cases e
      · rename_i hd hhd
        split at e
        · cases e
        · rename_i s hsf
          cases e
          refine ⟨?_, cutFold_nonce h _ _ _ _ _ _ s hsf (fun _ hm => by cases hm)⟩
          cases hsl : _root_.Fmt.slice b i 32 with
          | none => rw [hsl] at hx; cases hx
          | some rnd =>
            rw [hsl] at hx
            have hx' : (some rnd, i + 32) = (x, i0) := Option.some.inj hx
            have ex : x = some rnd := (Prod.mk.inj hx').1.symm
            subst ex
            exact ⟨_, (startChain_some h _ _ _ rnd hd hhd).2.1⟩

theorem fullWhole_facts (S : _root_.Fmt.Spec) (hr : S.rand = .inFile) (b : ByteArray) (o : ChainOut)
    (e : fullWhole (m := Id) h S b = some o) :
    (∃ x : ByteArray, o.run = some (h 172 0 S.label _root_.Fmt.zero32 x)) ∧
    ∀ ro ∈ o.rounds.toList, ro.nonce < 2 ^ 64 := by
  unfold fullWhole cutWhole at e
  simp only [idb] at e
  split at e
  · rename_i o' j hc
    have : o' = o := by
      simp only [idp] at e
      split at e
      · exact Option.some.inj e
      · cases e
    exact this ▸ cutChain_facts h _ S hr b 0 o' j hc
  · cases e

end

/-- For `ok S = true` (`hok`), the whole-path parser's string: a first salt of 256 bits, nonces
below 2^64. -/
theorem parse_factsW (S : _root_.Fmt.Spec) (C : CK) (dec : View → Bool) (hok : ok S = true)
    (file : ByteArray) (cm : Dig 256) (π : OneProtocolProof 256 (PSof C (rds S) dec).up)
    (e : parseFullWP (m := Id) _root_.Fmt.formatHash (PSof C (rds S) dec) S (TYS S C dec) file =
      some ([cm], π)) :
    π.salt.length = 256 ∧ noncesOK C (rds S) π.plains.2 := by
  have e' : (fullWhole (m := Id) _root_.Fmt.formatHash S file : Option ChainOut).bind
        (toBPrfFullP (PSof C (rds S) dec) (TYS S C dec)) =
      some ([cm], π) := e
  cases ho : (fullWhole (m := Id) _root_.Fmt.formatHash S file : Option ChainOut) with
  | none => rw [ho] at e'; cases e'
  | some o =>
    rw [ho] at e'
    obtain ⟨⟨x, hrun⟩, hnon⟩ := fullWhole_facts _root_.Fmt.formatHash S (rand_of_ok S hok) file o ho
    have e2 : toBPrfFullP (PSof C (rds S) dec) (TYS S C dec) o = some ([cm], π) := e'
    unfold toBPrfFullP at e2
    split at e2
    · rename_i run pl ops h1 h2 h3
      split at e2
      · have e3 := (Prod.mk.inj (Option.some.inj e2)).2
        rw [← e3]
        have hsz : run.size = 32 := by
          have : run = _root_.Fmt.formatHash 172 0 S.label _root_.Fmt.zero32 x :=
            Option.some.inj (h1.symm.trans hrun)
          rw [this]
          exact _root_.Fmt.size_H _ _ _ _ _
        have h2' : (plainsSL C (rds S) o.rounds.toList).map
              (fun r => (((), r) : Plains (Twin.up (SOf C (rds S))))) = some pl := h2
        cases hp : plainsSL C (rds S) o.rounds.toList with
        | none => rw [hp] at h2'; cases h2'
        | some r =>
          rw [hp] at h2'
          rw [← Option.some.inj h2']
          refine ⟨?_, nonces_of C (rds S) o.rounds.toList r hp hnon⟩
          show (bytesToBits run).length = 256
          rw [length_bytesToBits, hsz]
      · cases e2
    · cases e2

/-! ### The three statements -/

theorem oneW_is_typed : Spec.oneW_is_typed := by
  intro S C K chal dec file hok h hb
  simp only [fourBounds, Bool.and_eq_true, decide_eq_true_eq] at hb
  have F : FitsS S K := fitsS_of S K hok hb.1.1.1 hb.1.1.2 hb.1.2 hb.2
  rw [runFC_reader]
  unfold run1W
  cases e : parseFullWP (m := Id) _root_.Fmt.formatHash (PSof C (rds S) dec) S (TYS S C dec) file with
  | none =>
    unfold run1WOn runOnFC
    rw [dif_pos h]
  | some x =>
    unfold run1WOn runOnFC
    rw [dif_pos h, if_pos hok, if_pos hok]
    match x, e with
    | ([], _), _ => rfl
    | ([cm], π), e =>
      obtain ⟨h1, h2⟩ := parse_factsW S C dec hok file cm π e
      simp only
      rw [one_askedW S C K chal dec h cm π (asked_ofW S C K chal dec h F cm π h1 h2)]
    | (_ :: _ :: _, _), _ => rfl

theorem oneW_pull : Spec.oneW_pull := fun S dec file hok h hb =>
  (run1wpf_eq S dec file).trans (oneW_is_typed S _ _ _ dec file hok h hb)

theorem oneW_ck : Spec.oneW_ck := fun S dec file hok h hb =>
  (run1wf_eq S _ _ _ dec file).trans (oneW_is_typed S _ _ _ dec file hok h hb)

end Run.PQ
