# sudo PCMPGTB instruction bytes

The exact bytes in these files come from a retained Wruh extraction of sudo
1.9.17p2, `protobuf_c_message_unpack` (function ID `fn_00000000000357d0`,
relative entry address `0x357d0`). The binary SHA-256 is
`9bff0cd6e20204a361b4c8160ef8eb0c341355b391819b3b092120f5ed6cd797`.
Canonical addresses below are recorded by the extraction, not file offsets.

| Occurrence | Canonical address | Bytes | Instruction | Edge outcome |
| --- | --- | --- | --- | --- |
| 933 | `0x436cc5` | `66 0f 64 c6` | `pcmpgtb xmm0, xmm6` | 0 |
| 934 | `0x436cc9` | `66 0f 64 c8` | `pcmpgtb xmm1, xmm0` | 0 |

The original census reported unsupported `bvsgt` for the function. A later
rerun extracted it with Wruh revision `e687bdbe6dbeff229416b711a31c9c6d08fb3da9`
and AYXG revision `75caaf31a9df0f69ec92f7a167c7740cad891d14`. Both recorded
edges contain 16 `bv_slt` terms, but neither occurrence is established as the
exact site of the original failure. The retained `function-artifacts.tar.gz`
SHA-256 is `c74f4ba5ea6f56b58333120e36a2b1438c493b04fd6dbfd258e861c14465e3b6`;
member `functions/00000000000357d0.json` supplies the occurrence records.

The native comparison in `tests/native_pcmpgtb` uses these bytes to build fresh
stub extractions and supplies the same bytes to the shared native observer.
