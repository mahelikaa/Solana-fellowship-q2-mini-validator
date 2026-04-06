# Mini Solana Validator (Hard)

This project was built as part of the **Solana India Fellowship selection process (Question 2)**.

Build an in-memory, single-node Solana-compatible JSON-RPC server. Your server must accept **real Solana transactions** (the same binary wire format used by mainnet) and execute them against an in-memory ledger. It must support the **System Program**, **SPL Token Program**, and **Associated Token Account Program** — so that standard Solana client libraries (`@solana/web3.js`, `@solana/spl-token`) can interact with your server as if it were a real Solana cluster.

## JSON-RPC Protocol

Your server listens on port **3000** and accepts HTTP POST requests at the root path `/`. Every request is a JSON-RPC 2.0 object:

```json
{ "jsonrpc": "2.0", "id": 1, "method": "getBalance", "params": ["pubkeyBase58"] }
```

Every response must include `jsonrpc` and `id`. Successful responses have a `result` field. Errors have an `error` field with `code` and `message`.

### Error Codes
- `-32601` — Method not found
- `-32600` — Invalid request (malformed JSON, missing fields)
- `-32602` — Invalid params
- `-32003` — Transaction failed (signature verification, insufficient funds, etc.)

## RPC Methods to Implement

### Cluster Info
- **getVersion** → `{ "solana-core": "<version>", "feature-set": <number> }`
- **getSlot** → `<number>` — Current slot. Must increment after each processed transaction.
- **getBlockHeight** → `<number>` — Current block height.
- **getHealth** → `"ok"`

### Blockhash
- **getLatestBlockhash** — params: `[{ commitment }]`
  - Response: `{ context: { slot }, value: { blockhash: "<base58 string>", lastValidBlockHeight: <number> } }`
  - The blockhash can be any valid base58 string you generate. Your server must track which blockhashes it has issued and **reject transactions that use a blockhash the server never returned** from `getLatestBlockhash`.

### Account Queries
- **getBalance** — params: `[pubkeyBase58]`
  - Response: `{ context: { slot }, value: <lamports> }`
  - Return 0 for accounts that don't exist.

- **getAccountInfo** — params: `[pubkeyBase58, { encoding: "base64" }]`
  - Response: `{ context: { slot }, value: <AccountInfo | null> }`
  - `AccountInfo`: `{ data: ["<base64>", "base64"], executable: bool, lamports: number, owner: "<pubkeyBase58>", rentEpoch: number }`
  - Return `value: null` for accounts that don't exist.

- **getMinimumBalanceForRentExemption** — params: `[dataSize]`
  - Response: `<number>` — a fixed formula is fine, e.g. `(dataSize + 128) * 2` or any consistent positive number.

### Token Queries
- **getTokenAccountBalance** — params: `[pubkeyBase58]`
  - Response: `{ context: { slot }, value: { amount: "<string>", decimals: <number>, uiAmount: <number> } }`
  - Return JSON-RPC error if account doesn't exist or is not a token account.

- **getTokenAccountsByOwner** — params: `[ownerBase58, filter, { encoding: "base64" }]`
  - `filter` is either `{ mint: "<pubkeyBase58>" }` or `{ programId: "<pubkeyBase58>" }`
  - Response: `{ context: { slot }, value: [{ pubkey, account: <AccountInfo> }, ...] }`
  - Return empty array if no matching accounts.

### Transaction Submission
- **requestAirdrop** — params: `[pubkeyBase58, lamports]`
  - Credit the account with `lamports` SOL.
  - Response: `"<signatureBase58>"` — return any unique string as the signature.

- **sendTransaction** — params: `[encodedTx, { encoding: "base64", skipPreflight? }]`
  - Decode the base64-encoded transaction.
  - **Verify all signatures** using ed25519 — reject if any signature is invalid or missing (all zero).
  - Execute all instructions in order.
  - Response: `"<signatureBase58>"` — the first signature from the transaction.
  - Return JSON-RPC error (`-32003`) if execution fails.

- **getSignatureStatuses** — params: `[[sig1, sig2, ...]]`
  - Response: `{ context: { slot }, value: [status | null, ...] }`
  - For processed transactions: `{ slot, confirmations: null, err: null, confirmationStatus: "confirmed" }`
  - Return `null` for unknown signatures.

## Transaction Processing

When you receive a transaction via `sendTransaction`:

1. **Deserialize** the base64 bytes into a Solana transaction. You can use `@solana/web3.js`'s `Transaction.from()` or parse the wire format yourself.
2. **Verify signatures** — every required signer must have a valid ed25519 signature over the transaction message.
3. **Execute each instruction** sequentially:
   - Identify the program by its pubkey
   - Decode the instruction data according to that program's format
   - Modify the in-memory account state

## Programs to Implement

### System Program (`11111111111111111111111111111111`)

Instructions (discriminator is **u32 little-endian**):

- **CreateAccount** (discriminator `0`): `[u32 disc][u64 lamports][u64 space][32-byte owner pubkey]`
  - Debit `lamports` from the payer (first account).
  - Create a new account (second account) with the given `space`, `lamports`, and `owner`.
  - The new account must be a signer.
  - Fail if the account already exists (has lamports > 0 or data).

- **Transfer** (discriminator `2`): `[u32 disc][u64 lamports]`
  - Transfer `lamports` from first account to second account.
  - First account must be a signer.
  - Fail if insufficient balance.

### SPL Token Program (`TokenkegQfeZyiNwAJbNbGKPFXCWuBvf9Ss623VQ5DA`)

Instructions (discriminator is **u8**):

Token Account Data Layout (165 bytes):
```
[32 bytes mint][32 bytes owner][8 bytes amount (u64 LE)][36 bytes delegate option][1 byte state][12 bytes isNative option][8 bytes delegatedAmount (u64 LE)][36 bytes closeAuthority option]
```

Mint Data Layout (82 bytes):
```
[4 bytes mintAuthorityOption (u32 LE)][32 bytes mintAuthority][8 bytes supply (u64 LE)][1 byte decimals][1 byte isInitialized][4 bytes freezeAuthorityOption (u32 LE)][32 bytes freezeAuthority]
```

- **InitializeMint2** (discriminator `20`): `[u8 disc][u8 decimals][32 bytes mintAuthority][u8 hasFreezeAuth][32 bytes freezeAuthority]`
  - Accounts: `[mint]`
  - Set mint data: decimals, mintAuthority, supply=0, isInitialized=1.
  - Fail if already initialized.

- **InitializeAccount3** (discriminator `18`): `[u8 disc][32 bytes owner]`
  - Accounts: `[tokenAccount, mint]`
  - Initialize a token account with the given owner and mint, amount=0, state=initialized(1).

- **MintTo** (discriminator `7`): `[u8 disc][u64 amount LE]`
  - Accounts: `[mint, destination, authority]`
  - Authority must be the mint's mintAuthority and must be a signer.
  - Add `amount` to the destination token account's balance.
  - Add `amount` to the mint's supply.

- **Transfer** (discriminator `3`): `[u8 disc][u64 amount LE]`
  - Accounts: `[source, destination, owner]`
  - Owner must be a signer and must match the source token account's owner.
  - Debit source, credit destination.
  - Fail if insufficient token balance.

- **TransferChecked** (discriminator `12`): `[u8 disc][u64 amount LE][u8 decimals]`
  - Accounts: `[source, mint, destination, owner]`
  - Same as Transfer but also verifies `decimals` matches the mint's decimals.

- **Burn** (discriminator `8`): `[u8 disc][u64 amount LE]`
  - Accounts: `[tokenAccount, mint, owner]`
  - Owner must be a signer and match the token account's owner.
  - Debit token account, reduce mint supply.

- **CloseAccount** (discriminator `9`): no additional data
  - Accounts: `[account, destination, owner]`
  - Account balance must be 0.
  - Transfer remaining lamports to destination.
  - Delete the account.

### Associated Token Account Program (`ATokenGPvbdGVxr1b2hvZbsiqW5xWH25efTNsLJA8knL`)

- **Create** (discriminator `0` or empty instruction data):
  - Accounts: `[payer, ata, owner, mint, systemProgram, tokenProgram]`
  - Derive the ATA address as a PDA: `findProgramAddress([owner, TOKEN_PROGRAM_ID, mint], ATA_PROGRAM_ID)`
  - Verify the derived address matches the ATA account provided.
  - Create the account (allocate 165 bytes, assign to Token Program, fund with rent-exempt minimum).
  - Initialize it as a token account (set mint, owner, amount=0, state=1).
  - Fail if the ATA already exists.

## Account Model

Every account has:
- `pubkey` — the public key (address)
- `lamports` — SOL balance in lamports
- `owner` — the program that owns this account (default: System Program)
- `data` — byte array (empty for SOL accounts, 82 bytes for mints, 165 bytes for token accounts)
- `executable` — always `false` for user accounts

## Tech Stack
Node.js + Express (or any HTTP framework). All state in memory (no database needed).

## Dependencies
You may use `@solana/web3.js` server-side to help with transaction deserialization, PublicKey operations, and ed25519 helpers. You may also use `tweetnacl` for signature verification and `bs58` for base58 encoding/decoding.

## Start Command
```
npm install && npm start
```
Server must listen on port **3000**.

## 📊 Score

**63 / 64 test cases passed**
