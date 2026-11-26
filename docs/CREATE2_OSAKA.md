# CREATE2 target storage on Osaka

A target account with zero nonce and empty code does not collide merely because
its persistent storage is nonempty. The Osaka reference used here is Foundry
v1.5.0 (`anvil --hardfork osaka`). It accepts this target, retains its balance,
initializes persistent storage to empty before executing initcode, and commits
that empty storage when the constructor returns successfully. Nonzero nonce or
nonempty code still causes collision; failure retains the target snapshot and
increments the creator nonce.

The previous `Lambda` implementation applied the proposed EIP-7610 storage
collision condition unconditionally and retained old persistent storage in a
successful newly created account. Both behaviors disagree with this reference.
The fix changes the shared creation path; it does not introduce a new fork
selector or claim support for forks activating different collision rules.

Run the native regression and mutations:

```sh
python3 -m pip install -r requirements-native-tests.txt
lake build create2OsakaChecks EvmYul.FFI.ffi:dynlib
python3 scripts/check_create2_osaka_runtime.py --output .lake/create2-osaka-runtime
python3 scripts/check_create2_osaka_mutations.py --output .lake/create2-osaka-mutations
```

With Foundry v1.5.0 `anvil` and `cast` on `PATH`, independently capture all four
real-EVM cases:

```sh
python3 scripts/check_create2_osaka_reference.py --output .lake/create2-osaka-reference
```

Both instruments use creator `0x2001`, salt 7 and initcode
`600b380380600b5f395ff3`; the created address is
`0xe317ec6689ba1293927261f8acda33b2db0bb1ba`. The caller writes slot 7 from 23 to
99 before CREATE2. The four target cases are storage-only, balance-only, nonce
collision, and code collision. Every target starts with balance 19. Success
leaves target nonce 1 and empty code/storage, retaining balance 19; collision
preserves its old nonce, code, balance and slot 9. Native assertions also retain
original transaction storage and the created-account membership distinction.

The mutations compile actual copied production semantics in a separate
namespace. Restoring the storage collision check, dropping the storage reset,
or removing either nonce or code collision check must execute and fail an
unchanged regression assertion. Compilation failures are not detections, and
each detected runtime failure must repeat identically on replay.

This is component conformance, not a whole-transaction or Solidity importer
correctness theorem. It does not justify treating native execution as an oracle
for an independently computed canonical model.

The executable loads the existing elliptic-curve Python helpers during module
initialization even though these cases do not call elliptic-curve precompiles.
Install the documented Python dependencies before execution. The runtime
checker requires exactly the successful regression output and no stderr; it
rejects initialization panics even when the executable exits with status zero.
