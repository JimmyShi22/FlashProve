# A small proof under a clipped-gap policy

One proof for a small synthetic model under an acceptance policy that tolerates tokens other than the model's first choice. Such a policy is for replies that an ordinary floating-point engine served: that engine and the committed integer model do not always rank the same token first. Read [../accepted-proof/](../accepted-proof/README.md) first. No GPU is needed.

## Try it

From the repository's top directory, after `verifier/build.sh`:

```sh
bin/cp_verify examples/accepted-proof-clipped-gap/config examples/accepted-proof-clipped-gap/ivk \
  examples/accepted-proof-clipped-gap/example.req examples/accepted-proof-clipped-gap/example.y \
  examples/accepted-proof-clipped-gap/example.proof \
  -id 8df714349b76202d6f302bb80b33d6d0798bd81d987b9e387038b7fd24c55ae6 \
  -policy clipped-gap,9244130,323343,1,16,8 -q
```

The call ends with exit code 0. Its last four lines:

```
commitment: 49 closeness rounds of the one-time files rest on another source than the bound within a third of the distance; the table has a record: the binding of the weights rests on the theorem on codes (ePrint 2025/2055, Theorem 4.6), taken as given
proof of work: up to 32 bits counted in 38 rounds; with it the least round has 128.00 bits, without it 96.23 bits
result-v1 status=0 claim=policy id=8df714349b76202d6f302bb80b33d6d0798bd81d987b9e387038b7fd24c55ae6 bits=128 work=32 work-rounds=38 least-round=128.00 least-round-without-work=96.23 commitment-assumed-rounds=49 record=1 r=15 e=47 T=64 tokens=16..47 y=no policy=clipped-gap C=9244130 theta=323343 cap=1 s=16 sh=8 sT=4 F=24 above-clip=1 leaf=0 stages=key,leaf,request dw=8 build=<64 hex digits>
WITHIN LIMITS: clipped-gap C=9244130 theta=323343 cap=1 s=16 sh=8
```

The last line is the answer. `WITHIN LIMITS` is not `YES`, although the exit code is the same. The lines `commitment:` and `proof of work:` and the fields of `result-v1` are explained in [../accepted-proof/](../accepted-proof/README.md). As there, neither figure in the line `proof of work:` is a security level, and the bits that they print are the C++ programs' own accounting, not a theorem.

## The policy

The files are named as in `../accepted-proof/`. The commitment ID covers `policy.txt`, so each policy needs a commitment of its own.

The logit gap of a checked token is the largest logit at its position minus the token's own logit, plus 1 if a token with the largest logit has a lower token ID. It is 0 for the model's first choice. A token's cost is its logit gap plus 2^sh, here 256. Three lines of `policy.txt` limit the costs of the checked tokens:

| line | meaning |
|---|---|
| `C 9244130` | the clip: a cost above C counts as C |
| `theta 323343` | counted in this way, the costs average at most theta |
| `cap 1` | at most this many tokens cost more than C |

The exact match is the case C = theta = 2^sh and cap = 0: no token may cost more than a first choice does.

`-policy` states the policy that you expect: its kind, then the lines `C`, `theta`, `cap`, `s` and `sh`. If you leave the option out, or `policy.txt` sets other values, the call ends `NO: policy`, exit code 1. `s` states the unit of the logits: a logit of the model is an integer logit divided by 2^s. It is the provider's statement, and nothing in the proof ties it to the model.

## The request

`example.req` is made from [reply.json](../../prover/examples/target_small_f2_gap/reply.json): a prompt of 16 tokens, the reply of 32 tokens that a floating-point copy of the model gave to it, and token 0 up to 64 tokens; then r = 15 and e = 47. So the proof is about tokens 16 to 47, the whole reply. Four of them are not the integer model's first choice; the configuration's page gives their costs. Since e is below 64, the proof says nothing about the token after the request, and `example.y` holds 0.

## What WITHIN LIMITS says

It says that the costs of the checked tokens meet the three limits under the committed model. It does not say that any of them is the model's first choice. Lean's soundness theorem on `verify` is for exact match only, and is of the verifier written in Lean, not of `cp_verify`, and at full size only: not at this example's; for a policy such as the clipped gap, Lean's theorem says only that the output meets the policy, which by itself bars little ([limits](../../docs/limits.md#within-limits)).

The limits are set by whoever made the commitment. They bound costs that are measured on the committed model's logits, which no verifier sees. Where the logits lie close together, several tokens cost C or less, and any of them can stand at that place if the other tokens' costs leave room in the average. And under these limits one of the 32 tokens can be any token at all, if the others are first choices: the line `covered:` prints that as `above-clip=1`.

A reply that meets fitted limits says little about which of two nearby models served it; a reply that misses them says much. This was scored, not proved, on a small synthetic model: 42 to 54 of 64 replies of a slightly altered model met limits that were fitted at the fitting script's loosest setting (`--share 100`), against 62 to 64 of 64 honest replies (one alteration, one draw of prompts; the counts differ between machines, libraries and data types, and the lowest of each range is known from a report alone). Under such a policy each proof or refusal also tells something about the costs ([the configuration's page](../../prover/examples/target_small_f2_gap/README.md#what-the-counts-show-and-what-they-do-not)).

The three limits, `C`, `theta` and `cap`, were fitted for this example alone, on replies of a small floating-point model exported from the same made-up weights, and on no real model, so they say nothing about a real model's thresholds. How they were fitted, and how many honest and altered replies meet them: [prover/examples/target_small_f2_gap](../../prover/examples/target_small_f2_gap). Acceptance policies in a real check: [docs/verifying.md](../../docs/verifying.md#acceptance-policies).

As in `../accepted-proof/`, the model is synthetic, and the ID, the request and the values after `-policy` came in the same package as the proof. In real use, get the ID before you send the prompt, from the party that vouches for the model, not through the server you are checking (best from where the commitment is published); fix the limits that you accept before the proof is made; and never take either from the files that you are checking.

## How the files were made

At the configuration [prover/examples/target_small_f2_gap](../../prover/examples/target_small_f2_gap), with calls like the two in [../accepted-proof/README.md](../accepted-proof/README.md#how-the-files-were-made), on the same programs as there, which are not the released programs, under a seed of its own, in a secret directory of its own, of which the same holds. `config/` holds copies of that configuration's three files, and [THIRD_PARTY.md](../../THIRD_PARTY.md) lists on which of Meta's models they may depend.
