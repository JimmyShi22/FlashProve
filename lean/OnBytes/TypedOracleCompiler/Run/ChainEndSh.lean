-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Run/ChainEndSh.lean: a shared stretch of the typed verifier's chain that ends in a
sealed round and has no tail: its value from the chain as read.



Why. OnBytes/TypedOracleCompiler/Run/ChainFrom.lean has a local stretch with no tail (`chain_end_lo`);
OnBytes/TypedOracleCompiler/Run/ChainF.lean has a shared stretch that ends in a sealed round BEFORE A TAIL T
(`chain_from_shS_ind`). A verifier that walks its three chains by three calls runs the shared
stretch by itself. At T := [] the shape `SL C ds ++ []` is not `SL C ds` by unfolding, so that lemma
does not apply there without a cast. Here is the same lemma with no tail.

Main names:
  `annShE C ds`, `wShE C K chal ds`: the annotation and the wires of written rounds, all shared
    (only the shared part is sent), with no tail: `annShS`, `wShS` (OnBytes/TypedOracleCompiler/Slice/) without T.
  `annShE_eq`: that annotation is the library's `RAnn.ofShared .sh` in every round.
  `RowShE`: the row law: `RowShS` (ChainF.lean) without T: `RowAt` at all rounds but the last,
    `SealAt` at the last.
  `chain_end_shS_ind`, `chain_end_shS`: the chain's value over the stretch is the verifier messages
    ρ, the roots round by round (`rtShL`), and the phase "shared" whose chain value is THE SEAL;
    what ρ draws is what the reader drew, up to the seal's digest; the typed tests of work pass as
    the reader's do.

Limits: what the head of OnBytes/TypedOracleCompiler/Run/ChainF.lean lists under WHAT IS NOT SAID. The row law
`RowShE` on g is a hypothesis: no family is shown to have it here. Nothing on soundness.

Terms: lean/GLOSSARY.md.
-/
import OnBytes.TypedOracleCompiler.Run.ChainF

set_option autoImplicit false

namespace TypedOracleCompiler.Run.PQ
open Rom TypedOracleCompiler.Iop _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Run.Twin
  TypedOracleCompiler.Run.Thin
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run _root_.Run.PQ TypedOracleCompiler.Run
open _root_.Run.Twin (allLo)
open _root_.Fmt (Chain RoundOut ChainOut Item ItemValue)
open TypedOracleCompiler.Slice (shdS wireSh)

/-! ## The annotation, the wires and the row law, with no tail -/

/-- written rounds, all shared: only the shared part is sent; no tail -/
def annShE (C : CK) : (ds : List RD) → RoundSplits (uL C ds)
  | [] => PUnit.unit
  | d :: ds => (shdS (roundS C d), annShE C ds)

/-- It is the library's annotation "only the shared part is sent" in every round. -/
theorem annShE_eq (C : CK) : ∀ ds : List RD,
    annShE C ds = RoundSplits.const (RAnn.ofShared .sh) (uL C ds)
  | [] => rfl
  | d :: ds => congrArg (Prod.mk (shdS (roundS C d))) (annShE_eq C ds)

/-- a shared stretch's wires; no tail -/
def wShE (C : CK) (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k) :
    (ds : List RD) → RoundsQueryLayout 256 (K + 1) (uL C ds) (annShE C ds)
  | [] => ()
  | d :: ds => (wireSh C K chal d, wShE C K chal ds)

section LawE
variable {I X : Type} (Lf : Unit → BatchProtocolWithLeafBody I X) (C : CK) (K : ℕ) (g : Fam (typedOracleFamily 256 (K + 1) (Lf ())))
  (t : Tag) (O : ByteArray → ByteArray) (label : ℕ)

/-- **The row law of a shared stretch that ends in a sealed round, with no tail**: `RowAt` at all
rounds but the last, `SealAt` at the last. -/
def RowShE : (ds : List RD) →
    (PlainPart (uL C ds) (annShE C ds) → PlainPart (Compile.Batch.shapeOf (Lf ()) t) (annOf (Lf ()) t)) → ℕ → ℕ →
      Prop
  | [], _, _, _ => True
  | [d], embP, i, n => SealAt Lf C K g t O label d (fun pl => embP (.inl (.inl pl))) i n
  | d :: d' :: ds, embP, i, n =>
    RowAt Lf C K g t O label (fun ρ => .f5 ρ) d (fun pl => embP (.inl (.inl pl))) i n ∧
      RowShE (d' :: ds) (fun z => embP (.inr z)) (i + 1) (n + 1)

end LawE

section MainE
variable {I X : Type} (Lf : Unit → BatchProtocolWithLeafBody I X) (C : CK) (K : ℕ) (g : Fam (typedOracleFamily 256 (K + 1) (Lf ())))
  (early : X → X) (late : Option ℕ) (t : Tag) (cms : List (Dig 256)) (x : Option X) (salt : Bits)
  (rtreq : Dig 256) (O : ByteArray → ByteArray) (hO : ∀ s, (O s).size = 32) (P : _root_.Fmt.Plan)
  (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k) (hkit : KitFits P.field C K chal) (label : ℕ)

include hO hkit in
/-- **A SHARED STRETCH THAT ENDS IN A SEALED ROUND, WITH NO TAIL**: the typed chain value behind it
is THE SEAL. -/
theorem chain_end_shS_ind (cS : Dig 256) (rest : List (Dig 256)) :
    ∀ (ds : List RD) (rs : List _root_.Fmt.Round) (ros : List RoundOut) (i : ℕ) (c : Chain)
        (roots : Array ByteArray) (v : Bits)
        (embP : PlainPart (uL C ds) (annShE C ds) →
          PlainPart (Compile.Batch.shapeOf (Lf ()) t) (annOf (Lf ()) t))
        (pls : Plains (uL C ds)),
      SealLast ds → FitL ds rs →
      (∀ r ∈ rs, _root_.Fmt.blocksFor (_root_.Fmt.wordsAtMost r.entry r.kind) ≤ K) →
      RowShE Lf C K g t O label ds embP i (c.round + 1) → c.label = label →
      bitsToBytes v = c.rho → v.length = 256 →
      TraceL (_root_.Fmt.HO O) P rs ros c roots → plainsSL C ds ros = some pls →
      ∃ (ρ : Rho (uL C ds)) (v' : Bits),
        chainP Lf g early late t cms x salt rtreq (SL C ds) (annShE C ds) (wShE C K chal ds)
            embP i (.shr v cS)
            ((ros.flatMap fun r => _root_.Fmt.rootsOf r.vals).map bytesToDig ++ rest) pls =
          some (ρ, rtShL C ds ros, .shr v' cS) ∧
        SameButSeal (drawnSL C ds ρ) (ros.map (·.drawn)) ∧
        passSL C ds ρ = passL (_root_.Fmt.HO O) rs ros c ∧
        v' = List.ofFn (bytesToDig (sealOf (_root_.Fmt.HO O) rs ros c))
  | [], _, _, _, _, _, _, _, _, hs, _, _, _, _, _, _, _, _ => hs.elim
  | [_], [], _, _, _, _, _, _, _, _, hf, _, _, _, _, _, _, _ => hf.elim
  | [_], _ :: _, [], _, _, _, _, _, _, _, _, _, _, _, _, _, ht, _ => ht.elim
  | _ :: _ :: _, [], _, _, _, _, _, _, _, _, hf, _, _, _, _, _, _, _ => hf.elim
  | _ :: _ :: _, [_], _, _, _, _, _, _, _, _, hf, _, _, _, _, _, _, _ => hf.2.2.2.2.2.2.elim
  | _ :: _ :: _, _ :: _ :: _, [], _, _, _, _, _, _, _, _, _, _, _, _, _, ht, _ => ht.elim
  | _ :: _ :: _, _ :: _ :: _, [_], _, _, _, _, _, _, _, _, _, _, _, _, _, ht, _ =>
      ht.2.2.2.2.2.elim
  | [d], r :: rs, ro :: ros, i, c, roots, v, embP, (p, pls), hs, hf, hroom, hrow, hlab, hv, hv256,
      ht, hp => by
      obtain ⟨he, hk, hit, htree, hcount, h1, hf'⟩ := hf
      obtain ⟨hask, hwhole, hdrawn, -, -, ht'⟩ := ht
      cases rs with
      | cons _ _ => exact hf'.elim
      | nil =>
      cases ros with
      | cons _ _ => exact ht'.elim
      | nil =>
      rcases hp0 : PlainOf.ofGots d.items ro.vals with _ | p0
      · simp [plainsSL, hp0] at hp
      simp only [plainsSL, hp0, Option.some.injEq] at hp
      have hpa : GPlain.mk d.entry.work p0 ro.nonce = p := congrArg Prod.fst hp
      subst hpa
      simp only [_root_.Fmt.askOK, Bool.and_eq_true, and_assoc, decide_eq_true_iff,
        Bool.or_eq_true, bne_iff_ne, beq_iff_eq] at hask
      obtain ⟨-, -, -, -, -, hn64, hw0, -⟩ := hask
      have hwE : d.entry.work = r.entry.work := congrArg (·.work) he
      have hlen : (_root_.Fmt.rootsOf ro.vals).length = r.entry.roots := by
        rw [roots_ofGots d.items ro.vals p0 hp0, hit, hcount]
      have hsz := roots_size P.field r.items ro.msg ro.vals hwhole
      have hrt := map_dig_bytes (_root_.Fmt.rootsOf ro.vals) hsz
      have hN : GPlain.nonce (b := d.entry.work) (GPlain.mk d.entry.work p0 ro.nonce) = ro.nonce :=
        nonce_mk p0 ro.nonce d.entry.work (by rw [he]; exact hw0)
      have hM : bytesL (((_root_.Fmt.rootsOf ro.vals).map bytesToDig).map digToBytes) d.items
          (GPlain.old (b := d.entry.work) (GPlain.mk d.entry.work p0 ro.nonce)) = ro.msg := by
        rw [hrt, old_mk]
        exact (msg_bytes P.field d.items ro.msg ro.vals p0 (by rw [hit]; exact hwhole) hp0).1
      have hS := (hrow v ((_root_.Fmt.rootsOf ro.vals).map bytesToDig)
        (GPlain.mk d.entry.work p0 ro.nonce) hv256
        (by rw [List.length_map, hlen, htree]) (by rw [hN]; exact hn64)).trans
          (show _ = bytesToDig (_root_.Fmt.blockW (_root_.Fmt.HO O) c.label c.rho (c.round + 1)
            ro.msg r.kind r.entry.work ro.nonce 1) by rw [hM, hN, hv, hk, hwE, hlab])
      beta_reduce at hS
      have htake := takeRt_app (wireSh C K chal d).depth0.length
        ((_root_.Fmt.rootsOf ro.vals).map bytesToDig) rest
        (by rw [List.length_map, hlen]; exact (List.length_map _).trans htree)
        (by rw [List.length_map, hlen]; exact h1)
      refine ⟨((wireS C K chal d).chal
            (g (OracleName.fb t) (⟨i, .f5 v, (_root_.Fmt.rootsOf ro.vals).map bytesToDig,
                      embP (.inl (.inl (GPlain.mk d.entry.work p0 ro.nonce)))⟩ : FbIn 256 (Lf ()) t) :
                (Fin (K + 1) → Dig 256) × Dig 256).1, ()), _, ?_, ?_, ?_, rfl⟩
      · have hstep := chainP_shT Lf g early late t cms x salt rtreq (roundS C d) [] PUnit.unit
          (wireSh C K chal d) () embP i cS v _ _ _ (GPlain.mk d.entry.work p0 ro.nonce) pls htake _
          hS
        rw [List.flatMap_cons, List.flatMap_nil, List.append_nil]
        exact hstep
      · refine ⟨?_, trivial⟩
        show Alike (C.dr d.entry d.kind (GChal.old (b := d.entry.work)
          (chalGrind (chal d.entry d.kind) d.entry.work _))) ro.drawn
        obtain ⟨mb, hmb⟩ := old_some (chal d.entry d.kind) d.entry.work
          (g (OracleName.fb t) (⟨i, .f5 v, (_root_.Fmt.rootsOf ro.vals).map bytesToDig,
                      embP (.inl (.inl (GPlain.mk d.entry.work p0 ro.nonce)))⟩ : FbIn 256 (Lf ()) t) :
                (Fin (K + 1) → Dig 256) × Dig 256).1
        rw [hmb, hkit, hdrawn, ← he, ← hk]
        exact drawRound_alike P.field d.entry d.kind (by rw [hs.kind]; decide) hs.poss hs.trits
          hs.drawE hs.drawNZ _ _
      · show (GChal.pass (b := d.entry.work) (chalGrind (chal d.entry d.kind) d.entry.work _) &&
            true) = (_root_.Fmt.passesA r.entry.work (rowBs (_root_.Fmt.HO O) c r ro) && true)
        rw [pass_zero (chal d.entry d.kind) d.entry.work _ hs.work, ← hwE, hs.work]
        rfl
  | d :: d' :: ds, r :: r' :: rs, ro :: ro' :: ros, i, c, roots, v, embP, (p, pls), hs, hf, hroom,
      hrow, hlab, hv, hv256, ht, hp => by
      obtain ⟨he, hk, hit, htree, hcount, h1, hf'⟩ := hf
      obtain ⟨hask, hwhole, hdrawn, -, -, ht'⟩ := ht
      obtain ⟨hrow0, hrow'⟩ := hrow
      obtain ⟨p0, pl1, hp0, hp1, hp''⟩ := plainsSL_cons_some C hp
      have hpa : GPlain.mk d.entry.work p0 ro.nonce = p := (congrArg Prod.fst hp'').symm
      have hpb : pl1 = pls := (congrArg Prod.snd hp'').symm
      subst hpa
      obtain ⟨hlen, hnext, hdr0, hps0⟩ := round_factsG Lf C K g t O hO P chal hkit (fun ρ => .f5 ρ)
        d r ro c v (fun pl => embP (.inl (.inl pl))) i p0 he hk hit htree hcount
        (hroom r List.mem_cons_self) (by rw [hlab]; exact hrow0) hv hv256 hask hwhole hdrawn hp0
      have htake := takeRt_app (wireSh C K chal d).depth0.length
        ((_root_.Fmt.rootsOf ro.vals).map bytesToDig)
        (((ro' :: ros).flatMap fun r => _root_.Fmt.rootsOf r.vals).map bytesToDig ++ rest)
        (by rw [List.length_map, hlen]; exact (List.length_map _).trans htree)
        (by rw [List.length_map, hlen]; exact h1)
      obtain ⟨ρ', v'', hch, hdr, hps, hend⟩ :=
        chain_end_shS_ind cS rest (d' :: ds) (r' :: rs) (ro' :: ros) (i + 1)
          (nextOf (_root_.Fmt.HO O) c r ro) _ _ (fun z => embP (.inr z)) pls hs hf'
          (fun r' hr' => hroom r' (List.mem_cons_of_mem _ hr')) hrow' hlab hnext List.length_ofFn
          ht' (hp1.trans (congrArg some hpb))
      refine ⟨((wireS C K chal d).chal
            (g (OracleName.fb t) (⟨i, .f5 v, (_root_.Fmt.rootsOf ro.vals).map bytesToDig,
                      embP (.inl (.inl (GPlain.mk d.entry.work p0 ro.nonce)))⟩ : FbIn 256 (Lf ()) t) :
                (Fin (K + 1) → Dig 256) × Dig 256).1, ρ'), v'', ?_, ?_, ?_, hend⟩
      · have hstep := chainP_shG Lf g early late t cms x salt rtreq (roundS C d) (SL C (d' :: ds))
          (annShE C (d' :: ds)) (wireSh C K chal d) (wShE C K chal (d' :: ds)) embP i cS v _ _ _
          (GPlain.mk d.entry.work p0 ro.nonce) pls htake
        rw [List.flatMap_cons, List.map_append, List.append_assoc]
        exact hstep.trans (congrArg (Option.map _) hch)
      · exact ⟨hdr0, hdr⟩
      · exact congrArg₂ (· && ·) hps0 hps

include hO hkit in
/-- **The same over `StretchFacts`.** -/
theorem chain_end_shS (ds : List RD) (rs : List _root_.Fmt.Round) (ros : List RoundOut) (i : ℕ)
    (c : Chain) (roots : Array ByteArray) (v : Bits) (rest : List (Dig 256)) (cS : Dig 256)
    (embP : PlainPart (uL C ds) (annShE C ds) → PlainPart (Compile.Batch.shapeOf (Lf ()) t) (annOf (Lf ()) t))
    (pls : Plains (uL C ds)) (hs : SealLast ds) (F : StretchFacts O P C K ds rs ros c roots pls)
    (hrow : RowShE Lf C K g t O c.label ds embP i (c.round + 1))
    (hv : bitsToBytes v = c.rho) (hv256 : v.length = 256) :
    ∃ (ρ : Rho (uL C ds)) (v' : Bits),
      chainP Lf g early late t cms x salt rtreq (SL C ds) (annShE C ds) (wShE C K chal ds)
          embP i (.shr v cS)
          ((ros.flatMap fun r => _root_.Fmt.rootsOf r.vals).map bytesToDig ++ rest) pls =
        some (ρ, rtShL C ds ros, .shr v' cS) ∧
      SameButSeal (drawnSL C ds ρ) (ros.map (·.drawn)) ∧
      passSL C ds ρ = passL (_root_.Fmt.HO O) rs ros c ∧
      v' = List.ofFn (bytesToDig (sealOf (_root_.Fmt.HO O) rs ros c)) :=
  chain_end_shS_ind Lf C K g early late t cms x salt rtreq O hO P chal hkit c.label cS rest ds rs
    ros i c roots v embP pls hs F.fit F.room hrow rfl hv hv256 F.trace F.plains

end MainE

end TypedOracleCompiler.Run.PQ
