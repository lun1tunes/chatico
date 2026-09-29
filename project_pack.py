#!/usr/bin/env python3
"""Pack a project into an encrypted, copy-paste-safe archive and unpack it.

GitHub raw view drops C0 control bytes and truncates very long lines. The
mermaid bundle inside presentation/re-master.html has both (a raw 0x01 in a
string and lines of hundreds of kilobytes), so a plain-text archive comes
back corrupted after Ctrl+A. The archive is zlib-compressed, sealed with the
password, and wrapped as short ASCII lines. Split chunks on line boundaries;
paste them back together; unpack with the same --key.

Profiles (file selection only; the seal is the same):
  mas   this repo's deployment tree, split -ch → ~/chatico/o_allN
  pywp  the pywp runtime tree, split -ch → ~/chatico/p_allN
Auto-detected from the project root, or pass --profile.
One file: -f PATH pack split → {name}_all.txt and {name}_all1, {name}_all2, …
With -ch those land in ~/chatico under the file name, not o_all/p_all.
"""
from __future__ import annotations

import argparse
import base64
import hashlib
import hmac
import os
import re
import secrets
import struct
import subprocess
import tempfile
import zlib
from pathlib import Path, PurePosixPath

ARCHIVE_FILE = "all.txt"
ARCHIVE_MAGIC = "PROJECT_PACK_V3"
DEFAULT_CHUNK_SIZE = 1_000_000
WRAP = 76
SCRYPT_N = 1 << 14
SCRYPT_R = 8
SCRYPT_P = 1
_MAC_PREFIX = ARCHIVE_MAGIC.encode("ascii") + b"\0"
_B64_ALPHABET = frozenset(
    "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/="
)
_PASTE_JUNK = dict.fromkeys(map(ord, "\ufeff\u200b\u200c\u200d\u00a0"))
_HEADER_KEYS = ("kdf", "n", "r", "p", "salt", "nonce", "mac")

# Tests pin this. None → detect from the project root.
PROFILE: str | None = None
# split -ch writes these names into ~/chatico so both projects share one git repo.
CHUNK_TAGS = {"mas": "o", "pywp": "p"}

# --- mas ---------------------------------------------------------------

_MAS_PACK_DIRS = (
    "agents-template",
    "presentation",
    "mas-agent-kit",
    "excel-agent-tools",
    "fastapi-math-service",
    "mas-activity-service",
    "n8n",
    "schedule-builder-service",
    "tnav-cluster-service",
    "scripts",
)
_MAS_ROOT_FILES = (".env.example", "docs.md", "README.md", "docker-compose.yml", ".gitignore")
_MAS_NEVER_PREFIXES = ("simulation-model-example/",)
_MAS_EXCLUDED_DIRS = {
    ".git", ".venv", "venv", "__pycache__", ".mypy_cache", ".pytest_cache",
    ".ruff_cache", ".idea", ".cursor", "node_modules", "data", "task_binaries",
}
_MAS_EXCLUDED_FILES = {ARCHIVE_FILE, "conftest.py", ".coverage"}
_MAS_EXTENSIONS = {
    ".py", ".md", ".txt", ".json", ".js", ".css", ".html", ".csv", ".yml",
    ".yaml", ".toml", ".ini", ".cfg", ".bat", ".sh", ".inc", ".sch",
    ".grdecl", ".example", ".svg",
}
_MAS_NAMES = {
    "Dockerfile", ".dockerignore", ".gitattributes", ".gitignore",
    "requirements.txt", "requirements-dev.txt",
}

# --- pywp --------------------------------------------------------------

_PYWP_EXCLUDED_DIRS = {
    ".git", ".github", ".idea", ".mypy_cache", ".nox", ".pytest_cache",
    ".ruff_cache", ".tox", ".uv-cache", ".venv", ".vscode", ".windsurf",
    "__pycache__", "pywp.egg-info", "test_data", "tests", "venv",
}
_PYWP_EXCLUDED_PATHS = {"poetry.lock", "pyproject.toml", "pytest.ini", "uv.lock"}
_PYWP_EXCLUDED_FILES = {"conftest.py", "poetry.lock", "requirements-dev.txt"}
_PYWP_EXTENSIONS = {".cfg", ".css", ".html", ".inc", ".ini", ".js", ".json", ".py", ".toml", ".yaml", ".yml"}
_PYWP_NAMES = {
    "Dockerfile", "Procfile", "README.md", "constraints.txt", "requirements.txt",
    "runtime.txt", ".env.example",
}


def resolve_profile(root: Path, profile: str | None = None) -> str:
    chosen = profile if profile is not None else PROFILE
    if chosen is None:
        marker = root / "project_pack.profile"
        if marker.is_file():
            chosen = marker.read_text(encoding="utf-8").strip().splitlines()[0].strip()
        elif (root / "mas-activity-service").is_dir() or (root / "schedule-builder-service").is_dir():
            chosen = "mas"
        elif (root / "pywp").is_dir():
            chosen = "pywp"
        else:
            raise ValueError("Cannot detect project profile; pass --profile mas or --profile pywp")
    if chosen not in {"mas", "pywp"}:
        raise ValueError(f"Unknown profile: {chosen}")
    return chosen


def _mas_under_root(rel: Path) -> bool:
    posix = rel.as_posix()
    if posix.startswith(_MAS_NEVER_PREFIXES):
        return False
    if posix in _MAS_ROOT_FILES:
        return True
    return bool(rel.parts) and rel.parts[0] in _MAS_PACK_DIRS


def _mas_skip(path: Path, root: Path) -> bool:
    rel = path.relative_to(root)
    if not _mas_under_root(rel):
        return True
    if set(rel.parts) & _MAS_EXCLUDED_DIRS:
        return True
    if "tests" in rel.parts and rel.parts[0] not in {"n8n", "schedule-builder-service"}:
        return True
    if path.name in _MAS_EXCLUDED_FILES or path.name.endswith("_test.py"):
        return True
    if path.name.startswith("test_") and path.suffix.lower() == ".py":
        return rel.parts[0] in {"excel-agent-tools", "mas-activity-service"}
    if path.suffix == ".env" and not path.name.endswith(".env.example"):
        return True
    return False


def _mas_include(path: Path) -> bool:
    return path.name in _MAS_NAMES or path.name.endswith(".env.example") or path.suffix.lower() in _MAS_EXTENSIONS


def _git_list_candidates(root: Path) -> list[Path] | None:
    if not (root / ".git").exists():
        return None
    try:
        proc = subprocess.run(
            ["git", "-C", str(root), "ls-files", "-z", "--cached", "--others",
             "--exclude-standard", "--", *_MAS_PACK_DIRS, *_MAS_ROOT_FILES],
            check=True, capture_output=True,
        )
    except (OSError, subprocess.CalledProcessError):
        return None
    result = []
    for raw in proc.stdout.split(b"\0"):
        if raw:
            path = root / raw.decode("utf-8", errors="surrogateescape")
            if path.is_file():
                result.append(path)
    return result


def _git_ignored(root: Path, path: Path) -> bool:
    try:
        return subprocess.run(
            ["git", "-C", str(root), "check-ignore", "-q", "--", str(path.relative_to(root))],
            capture_output=True,
        ).returncode == 0
    except OSError:
        return False


def _collect_mas(root: Path, *, archive_path: Path | None) -> list[Path]:
    archive_paths = {(root / ARCHIVE_FILE).resolve()}
    if archive_path is not None:
        archive_paths.add(archive_path.resolve())
    candidates = _git_list_candidates(root)
    from_git = candidates is not None
    if candidates is None:
        candidates = [p for p in root.rglob("*") if p.is_file()]
    else:
        # presentation holds generated HTML (re-master.html) that gitignore drops.
        presentation = root / "presentation"
        if presentation.is_dir():
            candidates.extend(p for p in presentation.rglob("*") if p.is_file())
    files = []
    for path in candidates:
        if _mas_skip(path, root) or not _mas_include(path):
            continue
        if path.resolve() in archive_paths:
            continue
        if not from_git and _git_ignored(root, path):
            continue
        files.append(path)
    return sorted({p.resolve(): p for p in files}.values(), key=lambda p: p.relative_to(root).as_posix())


def _pywp_skip(path: Path, root: Path) -> bool:
    relative = path.relative_to(root)
    if set(relative.parts) & _PYWP_EXCLUDED_DIRS:
        return True
    if relative.as_posix() in _PYWP_EXCLUDED_PATHS:
        return True
    if path.name in _PYWP_EXCLUDED_FILES or "poetry" in path.name.lower():
        return True
    if path.name.startswith("test_") and path.suffix.lower() == ".py":
        return True
    if path.name.endswith("_test.py"):
        return True
    return path.is_symlink()


def _pywp_include(path: Path) -> bool:
    if path.name in _PYWP_NAMES or path.name.startswith("Dockerfile"):
        return True
    return path.suffix.lower() in _PYWP_EXTENSIONS


def _collect_pywp(root: Path, *, archive_path: Path | None) -> list[Path]:
    archive_resolved = archive_path.resolve() if archive_path is not None else None
    default_archive_resolved = (root / ARCHIVE_FILE).resolve()
    files: list[Path] = []
    for path in root.rglob("*"):
        if not path.is_file():
            continue
        if _pywp_skip(path, root) or not _pywp_include(path):
            continue
        resolved = path.resolve()
        if resolved == default_archive_resolved or resolved == archive_resolved:
            continue
        files.append(path)
    return sorted(set(files), key=lambda item: item.relative_to(root).as_posix())


def collect_files(root: Path, *, archive_path: Path | None = None, profile: str | None = None) -> list[Path]:
    name = resolve_profile(root, profile)
    if name == "mas":
        return _collect_mas(root, archive_path=archive_path)
    return _collect_pywp(root, archive_path=archive_path)


def _validate_rel(rel: str) -> None:
    if (
        not rel
        or "\x00" in rel
        or "\\" in rel
        or any(char in rel for char in "\r\n\t")
    ):
        raise ValueError(f"Invalid archive path: {rel!r}")
    path = PurePosixPath(rel)
    if path.is_absolute() or not path.parts or ".." in path.parts:
        raise ValueError(f"Invalid archive path: {rel!r}")


def encode_payload(records: list[tuple[str, bytes]]) -> bytes:
    out = bytearray(b"PP1\n")
    seen: set[str] = set()
    for rel, data in records:
        _validate_rel(rel)
        if rel in seen:
            raise ValueError(f"Invalid archive format: duplicate file {rel!r}")
        seen.add(rel)
        path_bytes = rel.encode("utf-8")
        out += struct.pack(">I", len(path_bytes))
        out += path_bytes
        out += struct.pack(">Q", len(data))
        out += data
        out += hashlib.sha256(data).digest()
    out += struct.pack(">I", 0)
    return bytes(out)


def decode_payload(blob: bytes) -> list[tuple[str, bytes]]:
    if not blob.startswith(b"PP1\n"):
        raise ValueError("Invalid archive format: bad payload")
    index = 4
    records: list[tuple[str, bytes]] = []
    seen: set[str] = set()
    while index + 4 <= len(blob):
        (path_len,) = struct.unpack(">I", blob[index:index + 4])
        index += 4
        if path_len == 0:
            if index != len(blob):
                raise ValueError("Invalid archive format: trailing payload")
            return records
        if path_len > 4096 or index + path_len + 8 > len(blob):
            raise ValueError("Invalid archive format: bad payload")
        rel = blob[index:index + path_len].decode("utf-8")
        index += path_len
        _validate_rel(rel)
        (data_len,) = struct.unpack(">Q", blob[index:index + 8])
        index += 8
        if data_len > 512 * 1024 * 1024 or index + data_len + 32 > len(blob):
            raise ValueError("Invalid archive format: bad payload")
        data = blob[index:index + data_len]
        index += data_len
        digest = blob[index:index + 32]
        index += 32
        if hashlib.sha256(data).digest() != digest:
            raise ValueError(f"Invalid archive format: checksum mismatch for {rel!r}")
        if rel in seen:
            raise ValueError(f"Invalid archive format: duplicate file {rel!r}")
        seen.add(rel)
        records.append((rel, data))
    raise ValueError("Invalid archive format: truncated payload")


def _require_key(key: str) -> None:
    if not isinstance(key, str) or key == "":
        raise ValueError("Key is required")


def _derive(key: str, salt: bytes) -> tuple[bytes, bytes]:
    master = hashlib.scrypt(
        key.encode("utf-8"),
        salt=salt,
        n=SCRYPT_N,
        r=SCRYPT_R,
        p=SCRYPT_P,
        dklen=64,
        maxmem=64 * 1024 * 1024,
    )
    return master[:32], master[32:]


def _xor(key: bytes, nonce: bytes, data: bytes) -> bytes:
    out = bytearray(len(data))
    view = memoryview(data)
    offset = 0
    counter = 0
    while offset < len(data):
        block = hmac.new(key, nonce + counter.to_bytes(8, "big"), hashlib.sha256).digest()
        take = min(32, len(data) - offset)
        for i in range(take):
            out[offset + i] = view[offset + i] ^ block[i]
        offset += take
        counter += 1
    return bytes(out)


def seal(payload: bytes, key: str) -> str:
    _require_key(key)
    salt = secrets.token_bytes(16)
    nonce = secrets.token_bytes(16)
    enc_key, mac_key = _derive(key, salt)
    ciphertext = _xor(enc_key, nonce, zlib.compress(payload, 6))
    mac = hmac.new(mac_key, _MAC_PREFIX + nonce + ciphertext, hashlib.sha256).digest()
    body = base64.b64encode(ciphertext).decode("ascii")
    lines = [
        ARCHIVE_MAGIC,
        "kdf scrypt",
        f"n {SCRYPT_N}",
        f"r {SCRYPT_R}",
        f"p {SCRYPT_P}",
        f"salt {base64.b64encode(salt).decode('ascii')}",
        f"nonce {base64.b64encode(nonce).decode('ascii')}",
        f"mac {base64.b64encode(mac).decode('ascii')}",
    ]
    lines.extend(body[i:i + WRAP] for i in range(0, len(body), WRAP))
    return "\n".join(lines) + "\n"


def _clean_line(line: str) -> str:
    return line.translate(_PASTE_JUNK).strip()


def open_sealed(raw: str, key: str) -> bytes:
    _require_key(key)
    text = raw.replace("\r\n", "\n").replace("\r", "\n")
    lines = [_clean_line(line) for line in text.split("\n")]
    while lines and lines[0] == "":
        lines.pop(0)
    if not lines or lines[0] != ARCHIVE_MAGIC:
        raise ValueError("Invalid archive format: missing header")
    header: dict[str, str] = {}
    body: list[str] = []
    in_body = False
    for line in lines[1:]:
        if line == "":
            continue
        if not in_body:
            key_name, sep, value = line.partition(" ")
            if sep and key_name in _HEADER_KEYS and key_name not in header:
                header[key_name] = value.strip()
                continue
            in_body = True
        if any(char not in _B64_ALPHABET for char in line):
            raise ValueError("Invalid archive format: corrupted data")
        body.append(line)
    expected = {
        "kdf": "scrypt",
        "n": str(SCRYPT_N),
        "r": str(SCRYPT_R),
        "p": str(SCRYPT_P),
    }
    if any(header.get(name) != value for name, value in expected.items()):
        raise ValueError("Invalid archive format: unexpected kdf")
    try:
        salt = base64.b64decode(header["salt"], validate=True)
        nonce = base64.b64decode(header["nonce"], validate=True)
        mac = base64.b64decode(header["mac"], validate=True)
        ciphertext = base64.b64decode("".join(body), validate=True)
    except (KeyError, ValueError) as exc:
        raise ValueError("Invalid archive format: corrupted data") from exc
    if len(salt) != 16 or len(nonce) != 16 or len(mac) != 32:
        raise ValueError("Invalid archive format: corrupted data")
    enc_key, mac_key = _derive(key, salt)
    expected_mac = hmac.new(mac_key, _MAC_PREFIX + nonce + ciphertext, hashlib.sha256).digest()
    if not hmac.compare_digest(expected_mac, mac):
        raise ValueError("Wrong key or corrupted archive")
    try:
        return zlib.decompress(_xor(enc_key, nonce, ciphertext))
    except zlib.error as exc:
        raise ValueError("Wrong key or corrupted archive") from exc


def _write_bytes_atomic(path: Path, data: bytes) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary_path: Path | None = None
    try:
        fd, name = tempfile.mkstemp(dir=path.parent, prefix=f".{path.name}.", suffix=".tmp")
        temporary_path = Path(name)
        with os.fdopen(fd, "wb") as handle:
            handle.write(data)
            handle.flush()
            os.fsync(handle.fileno())
        os.chmod(temporary_path, 0o644)
        os.replace(temporary_path, path)
        temporary_path = None
    finally:
        if temporary_path is not None:
            temporary_path.unlink(missing_ok=True)


def file_archive_names(path: Path) -> tuple[str, str]:
    name = path.name
    if not name or name in {".", ".."}:
        raise ValueError(f"Invalid file name: {path}")
    return f"{name}_all.txt", f"{name}_all"


def pack_one(root: Path, file_path: Path, output_file: Path, key: str) -> None:
    root = root.resolve()
    file_path = file_path.resolve()
    if not file_path.is_file():
        raise FileNotFoundError(f"File not found: {file_path}")
    try:
        rel = file_path.relative_to(root).as_posix()
    except ValueError as exc:
        raise ValueError(f"File is outside root: {file_path}") from exc
    _validate_rel(rel)
    payload = seal(encode_payload([(rel, file_path.read_bytes())]), key).encode("ascii")
    _write_bytes_atomic(output_file, payload)
    print(f"Packed 1 file into {output_file}")


def pack(root: Path, output_file: Path, key: str, *, profile: str | None = None) -> None:
    root = root.resolve()
    chosen = resolve_profile(root, profile)
    records = [
        (path.relative_to(root).as_posix(), path.read_bytes())
        for path in collect_files(root, archive_path=output_file, profile=chosen)
    ]
    _write_bytes_atomic(output_file, seal(encode_payload(records), key).encode("ascii"))
    print(f"Packed {len(records)} files [{chosen}] into {output_file}")


def _load_records(input_file: Path, key: str) -> list[tuple[str, bytes]]:
    if not input_file.is_file():
        raise FileNotFoundError(f"Archive file not found: {input_file}")
    text = input_file.read_bytes().decode("utf-8")
    return decode_payload(open_sealed(text, key))


def unpack(root: Path, input_file: Path, key: str) -> None:
    records = _load_records(input_file, key)
    root.mkdir(parents=True, exist_ok=True)
    root_resolved = root.resolve()
    planned: list[tuple[Path, bytes]] = []
    for rel, data in records:
        target = root.joinpath(*PurePosixPath(rel).parts).resolve()
        if root_resolved != target and root_resolved not in target.parents:
            raise ValueError(f"Refusing to unpack outside root: {rel}")
        planned.append((target, data))
    for target, data in planned:
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(data)
    print(f"Restored {len(records)} files from {input_file}")


def verify_archive(input_file: Path, key: str) -> int:
    count = len(_load_records(input_file, key))
    print(f"Archive is valid: {count} files in {input_file}")
    return count


def chatico_dir() -> Path:
    return Path.home() / "chatico"


def chatico_prefix(profile: str) -> str:
    try:
        tag = CHUNK_TAGS[profile]
    except KeyError as exc:
        raise ValueError(f"Unknown profile: {profile}") from exc
    return f"{tag}_all"


def _chunk_pattern(prefix: str) -> re.Pattern[str]:
    return re.compile(rf"^{re.escape(prefix)}([1-9][0-9]*)$")


def split_archive(
    input_file: Path,
    *,
    chunk_dir: Path | None = None,
    chunk_prefix: str | None = None,
    chunk_size: int = DEFAULT_CHUNK_SIZE,
) -> list[Path]:
    if not input_file.is_file():
        raise FileNotFoundError(f"Archive file not found: {input_file}")
    if chunk_size <= WRAP:
        raise ValueError("Chunk size must be a positive integer larger than one archive line")
    text = input_file.read_bytes().decode("utf-8").replace("\r\n", "\n").replace("\r", "\n")
    if text and not text.endswith("\n"):
        text += "\n"
    lines = text.split("\n")
    if lines and lines[-1] == "":
        lines.pop()
    chunks: list[str] = []
    current = ""
    for line in lines:
        piece = line + "\n"
        if len(piece.encode("utf-8")) > chunk_size:
            raise ValueError(f"Archive line is too large for a {chunk_size}-byte chunk")
        if current and len((current + piece).encode("utf-8")) > chunk_size:
            chunks.append(current)
            current = ""
        current += piece
    if current:
        chunks.append(current)
    if not chunks:
        chunks.append("")
    target = chunk_dir or input_file.parent
    target.mkdir(parents=True, exist_ok=True)
    prefix = chunk_prefix or input_file.stem
    pattern = _chunk_pattern(prefix)
    for path in target.iterdir():
        if path.is_file() and pattern.fullmatch(path.name):
            path.unlink()
    written: list[Path] = []
    for index, content in enumerate(chunks, start=1):
        path = target / f"{prefix}{index}"
        _write_bytes_atomic(path, content.encode("utf-8"))
        written.append(path)
    print(f"Split {input_file} into {len(written)} text chunks")
    return written


def collect_chunk_files(chunk_dir: Path, chunk_prefix: str) -> list[Path]:
    pattern = _chunk_pattern(chunk_prefix)
    matches: list[tuple[int, Path]] = []
    for path in chunk_dir.iterdir():
        if not path.is_file():
            continue
        match = pattern.fullmatch(path.name)
        if match is not None:
            matches.append((int(match.group(1)), path))
    if not matches:
        raise FileNotFoundError(
            f"Archive chunks not found in {chunk_dir} with prefix {chunk_prefix!r}"
        )
    matches.sort(key=lambda item: item[0])
    for expected_index, (actual_index, path) in enumerate(matches, start=1):
        if actual_index != expected_index:
            raise ValueError(
                "Archive chunks are incomplete or out of order: expected "
                f"{chunk_prefix}{expected_index}, found {path.name}"
            )
    return [path for _, path in matches]


def join_archive(
    output_file: Path,
    *,
    chunk_dir: Path | None = None,
    chunk_prefix: str | None = None,
) -> list[Path]:
    directory = chunk_dir or output_file.parent
    prefix = chunk_prefix or output_file.stem
    paths = collect_chunk_files(directory, prefix)
    # Chunks are ASCII lines. Extra newlines from a manual paste are ignored
    # when the seal is opened; joining itself only concatenates.
    _write_bytes_atomic(output_file, b"".join(path.read_bytes() for path in paths))
    print(f"Joined {len(paths)} chunks into {output_file}")
    return paths


def _parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Pack, split, join, verify, or unpack an encrypted project archive."
    )
    parser.add_argument(
        "mode",
        nargs="+",
        choices=("pack", "unpack", "split", "join", "verify"),
    )
    parser.add_argument("--root", default=".")
    parser.add_argument("--archive", default=None)
    parser.add_argument(
        "-f",
        "--file",
        default=None,
        help="pack/split/join/unpack this one file as {name}_all.txt and {name}_allN",
    )
    parser.add_argument("--chunk-dir", default=None)
    parser.add_argument("--chunk-prefix", default=None)
    parser.add_argument("--chunk-size", type=int, default=DEFAULT_CHUNK_SIZE)
    parser.add_argument(
        "-ch",
        action="store_true",
        help="split/join chunks in ~/chatico as o_allN (mas) or p_allN (pywp)",
    )
    parser.add_argument("--key", default=None, help="Password. Required for pack, unpack, and verify.")
    parser.add_argument("--profile", choices=("mas", "pywp"), default=None)
    return parser.parse_args()


def _one_file(root: Path, raw: str) -> Path:
    path = Path(raw)
    if not path.is_absolute():
        path = root / path
    path = path.resolve()
    if not path.is_file():
        raise SystemExit(f"error: file not found: {path}")
    try:
        path.relative_to(root.resolve())
    except ValueError:
        raise SystemExit(f"error: file is outside root: {path}")
    return path


def main() -> None:
    args = _parse_args()
    modes = list(args.mode)
    root = Path(args.root).resolve()
    one = _one_file(root, args.file) if args.file else None
    one_archive_name = None
    one_prefix = None
    if one is not None:
        one_archive_name, one_prefix = file_archive_names(one)
    if args.ch and not ({"split", "join"} & set(modes)):
        raise SystemExit("error: -ch applies to split and join")
    if args.archive:
        archive = Path(args.archive).resolve()
    elif one_archive_name is not None:
        archive = (chatico_dir() if args.ch else root) / one_archive_name
    else:
        archive = root / ARCHIVE_FILE
    chunk_prefix = args.chunk_prefix
    if args.chunk_dir:
        chunk_dir = Path(args.chunk_dir).resolve()
    elif args.ch:
        chunk_dir = chatico_dir()
    else:
        chunk_dir = archive.parent
    if chunk_prefix is None and one_prefix is not None:
        chunk_prefix = one_prefix
    elif args.ch and chunk_prefix is None:
        chunk_prefix = chatico_prefix(resolve_profile(root, args.profile))
    if ({"pack", "unpack", "verify"} & set(modes)) and not args.key:
        raise SystemExit("error: --key is required for pack, unpack, and verify")
    for mode in modes:
        if mode == "pack":
            if one is None:
                pack(root, archive, args.key, profile=args.profile)
            else:
                pack_one(root, one, archive, args.key)
        elif mode == "unpack":
            unpack(root, archive, args.key)
        elif mode == "split":
            split_archive(
                archive,
                chunk_dir=chunk_dir,
                chunk_prefix=chunk_prefix,
                chunk_size=args.chunk_size,
            )
        elif mode == "join":
            join_archive(archive, chunk_dir=chunk_dir, chunk_prefix=chunk_prefix)
        else:
            verify_archive(archive, args.key)


if __name__ == "__main__":
    main()
