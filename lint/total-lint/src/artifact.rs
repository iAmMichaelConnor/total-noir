//! Decoding of nargo program artifacts.
//!
//! A program artifact is JSON with these fields:
//! - `bytecode`: base64 of a gzip stream holding the serialized ACIR
//!   `Program` (acir's own deserializer handles the format byte).
//! - `debug_symbols`: base64 of a raw DEFLATE stream (no gzip header)
//!   holding JSON `{"debug_infos": [DebugInfo, ...]}`, one entry per ACIR
//!   function. Only the location fields are read here.
//! - `file_map`: file id (as a string key) to `{source, path, ...}`.
//! - `abi`: kept as raw JSON; `abi.error_types` maps assertion selectors
//!   to messages.
//!
//! A contract artifact has the same `file_map` and `noir_version` at the
//! top level and a `functions` array whose entries each carry `name`,
//! `is_unconstrained`, `abi`, `bytecode` and `debug_symbols`.

use std::collections::BTreeMap;
use std::io::Read;
use std::sync::Arc;

use acir::FieldElement;
use acir::circuit::Program;
use base64::Engine;
use serde::Deserialize;

/// A source span inside one file.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Location {
    pub file: u32,
    pub start: u32,
}

#[derive(Clone, Debug)]
pub struct SourceFile {
    pub path: String,
    pub source: String,
    line_starts: Vec<usize>,
}

impl SourceFile {
    pub fn new(path: String, source: String) -> Self {
        let mut line_starts = vec![0];
        for (i, b) in source.bytes().enumerate() {
            if b == b'\n' {
                line_starts.push(i + 1);
            }
        }
        SourceFile {
            path,
            source,
            line_starts,
        }
    }

    /// 1-based (line, column) of a byte offset.
    pub fn line_col(&self, offset: u32) -> (usize, usize) {
        let offset = (offset as usize).min(self.source.len());
        let line = match self.line_starts.binary_search(&offset) {
            Ok(i) => i,
            Err(i) => i - 1,
        };
        (line + 1, offset - self.line_starts[line] + 1)
    }

    /// Number of lines (a trailing newline starts an empty last line).
    pub fn line_count(&self) -> usize {
        self.line_starts.len()
    }

    /// Text of a 1-based line, without the newline.
    pub fn line_text(&self, line: usize) -> &str {
        if line == 0 || line > self.line_starts.len() {
            return "";
        }
        let start = self.line_starts[line - 1];
        let end = self
            .line_starts
            .get(line)
            .map(|e| e - 1)
            .unwrap_or(self.source.len());
        self.source
            .get(start..end.max(start))
            .unwrap_or("")
            .trim_end_matches('\r')
    }
}

#[derive(Clone, Debug)]
struct LocationNode {
    parent: Option<usize>,
    value: Location,
}

/// Location data for one ACIR function.
#[derive(Clone, Debug, Default)]
pub struct DebugInfo {
    /// ACIR opcode index -> call stack id.
    pub acir_locations: BTreeMap<usize, usize>,
    /// Brillig function id -> (Brillig opcode index -> call stack id).
    pub brillig_locations: BTreeMap<u32, BTreeMap<usize, usize>>,
    tree: Vec<LocationNode>,
}

impl DebugInfo {
    /// Call stack for a call stack id, outermost frame first. The tree's
    /// root node is a placeholder and is not part of any stack.
    pub fn call_stack(&self, id: usize) -> Vec<Location> {
        let mut out = Vec::new();
        let mut cur = id;
        let mut guard = 0;
        while let Some(node) = self.tree.get(cur) {
            let Some(parent) = node.parent else { break };
            out.push(node.value);
            cur = parent;
            guard += 1;
            if guard > self.tree.len() {
                break;
            }
        }
        out.reverse();
        out
    }
}

/// The nargo version whose ACIR lowering this tool is built and tested
/// against. Artifacts from other versions decode, but the shapes the
/// classifier recognises are only checked against this one.
pub const SUPPORTED_NOIR_VERSION: &str = "1.0.0-rc.3";

/// One ACIR program: a program artifact, or one function of a contract.
pub struct Artifact {
    /// `main` for a program artifact, the function name for a contract.
    pub name: String,
    pub noir_version: String,
    pub abi: serde_json::Value,
    pub program: Program<FieldElement>,
    pub debug: Vec<DebugInfo>,
    /// Shared between the functions of a contract.
    pub files: Arc<BTreeMap<u32, SourceFile>>,
}

/// What an artifact file holds.
pub enum Loaded {
    Program(Artifact),
    Contract {
        name: String,
        noir_version: String,
        /// Constrained functions, in artifact order.
        functions: Vec<Artifact>,
        /// Names of the unconstrained functions, which have no ACIR to lint.
        unconstrained: Vec<String>,
    },
}

impl Loaded {
    pub fn noir_version(&self) -> &str {
        match self {
            Loaded::Program(a) => &a.noir_version,
            Loaded::Contract { noir_version, .. } => noir_version,
        }
    }

    /// A warning when the artifact comes from another nargo version.
    pub fn version_warning(&self) -> Option<String> {
        version_warning(self.noir_version())
    }
}

/// A warning when `version` is not the supported nargo version.
pub fn version_warning(version: &str) -> Option<String> {
    let base = version.split('+').next().unwrap_or("");
    (base != SUPPORTED_NOIR_VERSION).then(|| {
        format!(
            "artifact compiled by noir {version:?}; total-lint is built and tested against {SUPPORTED_NOIR_VERSION} only, so its pattern recognition may misclassify this artifact"
        )
    })
}

#[derive(Deserialize)]
struct RawArtifact {
    #[serde(default)]
    noir_version: String,
    #[serde(default)]
    name: Option<String>,
    #[serde(default)]
    abi: serde_json::Value,
    bytecode: Option<String>,
    #[serde(default)]
    debug_symbols: Option<String>,
    #[serde(default)]
    file_map: BTreeMap<String, RawFile>,
    #[serde(default)]
    functions: Option<Vec<RawFunction>>,
}

#[derive(Deserialize)]
struct RawFunction {
    name: String,
    #[serde(default)]
    is_unconstrained: bool,
    #[serde(default)]
    abi: serde_json::Value,
    #[serde(default)]
    bytecode: String,
    #[serde(default)]
    debug_symbols: Option<String>,
}

/// Prefix aztec-nr's macros give the functions they generate.
const AZTEC_PREFIX: &str = "__aztec_nr_internals__";

#[derive(Deserialize)]
struct RawFile {
    source: String,
    path: String,
}

#[derive(Deserialize)]
struct RawProgramDebugInfo {
    debug_infos: Vec<RawDebugInfo>,
}

#[derive(Deserialize)]
struct RawDebugInfo {
    #[serde(default)]
    acir_locations: BTreeMap<String, usize>,
    #[serde(default)]
    brillig_locations: BTreeMap<String, BTreeMap<String, usize>>,
    location_tree: RawLocationTree,
}

#[derive(Deserialize)]
struct RawLocationTree {
    locations: Vec<RawLocationNode>,
}

#[derive(Deserialize)]
struct RawLocationNode {
    parent: Option<usize>,
    value: RawLocation,
}

#[derive(Deserialize)]
struct RawLocation {
    span: RawSpan,
    file: u32,
}

#[derive(Deserialize)]
struct RawSpan {
    start: u32,
}

fn parse_key<T: std::str::FromStr>(key: &str, what: &str) -> Result<T, String> {
    key.parse()
        .map_err(|_| format!("debug_symbols: bad {what} key {key:?}"))
}

/// Decode the `debug_symbols` field: base64, raw DEFLATE, JSON.
pub fn decode_debug_symbols(encoded: &str) -> Result<Vec<DebugInfo>, String> {
    decode_debug_symbols_capped(encoded, MAX_DECOMPRESSED)
}

/// `decode_debug_symbols` with a decompressed-size limit of `cap` bytes.
pub fn decode_debug_symbols_capped(encoded: &str, cap: u64) -> Result<Vec<DebugInfo>, String> {
    let compressed = base64::engine::general_purpose::STANDARD
        .decode(encoded.trim())
        .map_err(|e| format!("debug_symbols: base64: {e}"))?;
    let mut json = Vec::new();
    flate2::read::DeflateDecoder::new(&compressed[..])
        .take(cap + 1)
        .read_to_end(&mut json)
        .map_err(|e| format!("debug_symbols: deflate: {e}"))?;
    if json.len() as u64 > cap {
        return Err(format!(
            "debug_symbols: decompresses to more than {cap} bytes"
        ));
    }
    let raw: RawProgramDebugInfo =
        serde_json::from_slice(&json).map_err(|e| format!("debug_symbols: json: {e}"))?;
    raw.debug_infos
        .into_iter()
        .map(|d| {
            let mut acir_locations = BTreeMap::new();
            for (k, v) in d.acir_locations {
                acir_locations.insert(parse_key(&k, "acir location")?, v);
            }
            let mut brillig_locations = BTreeMap::new();
            for (k, inner) in d.brillig_locations {
                let mut m = BTreeMap::new();
                for (pc, v) in inner {
                    m.insert(parse_key(&pc, "brillig location")?, v);
                }
                brillig_locations.insert(parse_key(&k, "brillig function")?, m);
            }
            let tree = d
                .location_tree
                .locations
                .into_iter()
                .map(|n| LocationNode {
                    parent: n.parent,
                    value: Location {
                        file: n.value.file,
                        start: n.value.span.start,
                    },
                })
                .collect();
            Ok(DebugInfo {
                acir_locations,
                brillig_locations,
                tree,
            })
        })
        .collect()
}

/// Largest decompressed size accepted for bytecode or debug symbols, so a
/// crafted artifact cannot exhaust memory.
pub const MAX_DECOMPRESSED: u64 = 512 << 20;

/// Decode the `bytecode` field: base64 of a gzip-compressed serialized Program.
pub fn decode_bytecode(encoded: &str) -> Result<Program<FieldElement>, String> {
    decode_bytecode_capped(encoded, MAX_DECOMPRESSED)
}

/// `decode_bytecode` with a decompressed-size limit of `cap` bytes.
pub fn decode_bytecode_capped(encoded: &str, cap: u64) -> Result<Program<FieldElement>, String> {
    let bytes = base64::engine::general_purpose::STANDARD
        .decode(encoded.trim())
        .map_err(|e| format!("bytecode: base64: {e}"))?;
    // acir decompresses again internally; measure first with a cap.
    let size = std::io::copy(
        &mut flate2::read::GzDecoder::new(&bytes[..]).take(cap + 1),
        &mut std::io::sink(),
    )
    .map_err(|e| format!("bytecode: gzip: {e}"))?;
    if size > cap {
        return Err(format!("bytecode: decompresses to more than {cap} bytes"));
    }
    Program::deserialize_program(&bytes).map_err(|e| format!("bytecode: {e}"))
}

/// Name of the Brillig (unconstrained) function with this id.
pub fn brillig_name(program: &Program<FieldElement>, id: u32) -> Option<&str> {
    program
        .unconstrained_functions
        .get(id as usize)
        .map(|b| b.function_name.as_str())
}

fn decode_debug(symbols: Option<String>) -> Result<Vec<DebugInfo>, String> {
    match symbols {
        Some(s) if !s.is_empty() => decode_debug_symbols(&s),
        _ => Ok(Vec::new()),
    }
}

impl Loaded {
    pub fn from_json(text: &str) -> Result<Loaded, String> {
        let raw: RawArtifact =
            serde_json::from_str(text).map_err(|e| format!("artifact json: {e}"))?;
        let mut files = BTreeMap::new();
        for (k, f) in raw.file_map {
            files.insert(
                parse_key(&k, "file_map")?,
                SourceFile::new(f.path, f.source),
            );
        }
        let files = Arc::new(files);
        if let Some(bytecode) = raw.bytecode {
            let artifact = Artifact {
                name: "main".into(),
                noir_version: raw.noir_version,
                abi: raw.abi,
                program: decode_bytecode(&bytecode)?,
                debug: decode_debug(raw.debug_symbols)?,
                files,
            };
            artifact.check_abi()?;
            return Ok(Loaded::Program(artifact));
        }
        let Some(raw_functions) = raw.functions else {
            return Err("artifact has neither a bytecode field nor a functions list".into());
        };
        let mut functions = Vec::new();
        let mut unconstrained = Vec::new();
        for f in raw_functions {
            let name = f
                .name
                .strip_prefix(AZTEC_PREFIX)
                .unwrap_or(&f.name)
                .to_string();
            if f.is_unconstrained {
                unconstrained.push(name);
                continue;
            }
            let artifact = Artifact {
                program: decode_bytecode(&f.bytecode).map_err(|e| format!("{name}: {e}"))?,
                debug: decode_debug(f.debug_symbols).map_err(|e| format!("{name}: {e}"))?,
                name,
                noir_version: raw.noir_version.clone(),
                abi: f.abi,
                files: files.clone(),
            };
            artifact
                .check_abi()
                .map_err(|e| format!("{}: {e}", artifact.name))?;
            functions.push(artifact);
        }
        Ok(Loaded::Contract {
            name: raw.name.unwrap_or_default(),
            noir_version: raw.noir_version,
            functions,
            unconstrained,
        })
    }

    pub fn from_path(path: &str) -> Result<Loaded, String> {
        let text = std::fs::read_to_string(path).map_err(|e| format!("{path}: {e}"))?;
        Loaded::from_json(&text)
    }
}

impl Artifact {
    /// A program artifact; an error for a contract artifact.
    pub fn from_json(text: &str) -> Result<Artifact, String> {
        match Loaded::from_json(text)? {
            Loaded::Program(a) => Ok(a),
            Loaded::Contract { .. } => Err("this is a contract artifact".into()),
        }
    }

    pub fn from_path(path: &str) -> Result<Artifact, String> {
        let text = std::fs::read_to_string(path).map_err(|e| format!("{path}: {e}"))?;
        Artifact::from_json(&text)
    }

    /// Name of the Brillig function with this id.
    pub fn brillig_name(&self, id: u32) -> Option<&str> {
        brillig_name(&self.program, id)
    }

    /// Message for an assertion error selector, from abi.error_types.
    pub fn error_message(&self, selector: u64) -> Option<String> {
        let entry = self.abi.get("error_types")?.get(selector.to_string())?;
        match entry.get("error_kind")?.as_str()? {
            "string" => entry.get("string")?.as_str().map(str::to_string),
            "fmtstring" => entry.get("length").map(|_| "formatted message".to_string()),
            _ => Some("custom error type".to_string()),
        }
    }

    /// Selectors the ABI knows, used to name Brillig trap sites.
    pub fn error_selectors(&self) -> Vec<(u64, String)> {
        let mut out = Vec::new();
        if let Some(map) = self.abi.get("error_types").and_then(|m| m.as_object()) {
            for k in map.keys() {
                if let Ok(sel) = k.parse::<u64>()
                    && let Some(msg) = self.error_message(sel)
                {
                    out.push((sel, msg));
                }
            }
        }
        out
    }
}

/// One flattened entry-point parameter element, in witness order.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EntryParam {
    /// Display name, e.g. `amount_in`, `table[2]`, `pool.x`.
    pub name: String,
    /// Display type, e.g. `u64`, `bool`, `Field`.
    pub ty: String,
    /// Bit width the ABI type implies (integers, booleans, string bytes).
    pub width: Option<u32>,
}

fn str_of(v: Option<&serde_json::Value>) -> Result<&str, AbiError> {
    v.and_then(|v| v.as_str()).ok_or(AbiError::Unreadable)
}

fn u64_of(v: Option<&serde_json::Value>) -> Result<u64, AbiError> {
    v.and_then(|v| v.as_u64()).ok_or(AbiError::Unreadable)
}

/// Why an ABI could not be flattened.
enum AbiError {
    /// Not the shape this tool reads.
    Unreadable,
    /// More elements than the cap: the ABI cannot describe the entry
    /// function, and expanding it could exhaust memory.
    TooLarge,
}

fn push(out: &mut Vec<EntryParam>, cap: usize, p: EntryParam) -> Result<(), AbiError> {
    if out.len() >= cap {
        return Err(AbiError::TooLarge);
    }
    out.push(p);
    Ok(())
}

fn flatten_abi_type(
    name: &str,
    ty: &serde_json::Value,
    out: &mut Vec<EntryParam>,
    cap: usize,
) -> Result<(), AbiError> {
    match str_of(ty.get("kind"))? {
        "field" => push(
            out,
            cap,
            EntryParam {
                name: name.to_string(),
                ty: "Field".into(),
                width: None,
            },
        )?,
        "boolean" => push(
            out,
            cap,
            EntryParam {
                name: name.to_string(),
                ty: "bool".into(),
                width: Some(1),
            },
        )?,
        "integer" => {
            let width =
                u32::try_from(u64_of(ty.get("width"))?).map_err(|_| AbiError::Unreadable)?;
            let signed = ty.get("sign").and_then(|s| s.as_str()) == Some("signed");
            let t = format!("{}{width}", if signed { "i" } else { "u" });
            push(
                out,
                cap,
                EntryParam {
                    name: name.to_string(),
                    ty: t,
                    width: Some(width),
                },
            )?;
        }
        "string" => {
            for i in 0..u64_of(ty.get("length"))? {
                push(
                    out,
                    cap,
                    EntryParam {
                        name: format!("{name}[{i}]"),
                        ty: "u8".into(),
                        width: Some(8),
                    },
                )?;
            }
        }
        "array" => {
            let elem = ty.get("type").ok_or(AbiError::Unreadable)?;
            for i in 0..u64_of(ty.get("length"))? {
                flatten_abi_type(&format!("{name}[{i}]"), elem, out, cap)?;
            }
        }
        "struct" => {
            let fields = ty
                .get("fields")
                .and_then(|f| f.as_array())
                .ok_or(AbiError::Unreadable)?;
            for f in fields {
                let field_ty = f.get("type").ok_or(AbiError::Unreadable)?;
                flatten_abi_type(
                    &format!("{name}.{}", str_of(f.get("name"))?),
                    field_ty,
                    out,
                    cap,
                )?;
            }
        }
        "tuple" => {
            let fields = ty
                .get("fields")
                .and_then(|f| f.as_array())
                .ok_or(AbiError::Unreadable)?;
            for (i, f) in fields.iter().enumerate() {
                flatten_abi_type(&format!("{name}.{i}"), f, out, cap)?;
            }
        }
        _ => return Err(AbiError::Unreadable),
    }
    Ok(())
}

impl Artifact {
    /// Witness count of the entry function's parameters.
    fn entry_param_count(&self) -> usize {
        self.program
            .functions
            .first()
            .map(|f| f.private_parameters.len() + f.public_parameters.0.len())
            .unwrap_or(0)
    }

    /// Flatten the ABI parameters, stopping one element past the entry
    /// function's parameter count.
    fn flatten_params(&self) -> Result<Vec<EntryParam>, AbiError> {
        let cap = self.entry_param_count() + 1;
        let mut out = Vec::new();
        let params = self
            .abi
            .get("parameters")
            .and_then(|p| p.as_array())
            .ok_or(AbiError::Unreadable)?;
        for p in params {
            let name = p
                .get("name")
                .and_then(|n| n.as_str())
                .ok_or(AbiError::Unreadable)?;
            let ty = p.get("type").ok_or(AbiError::Unreadable)?;
            flatten_abi_type(name, ty, &mut out, cap)?;
        }
        Ok(out)
    }

    /// An error when the ABI describes more parameter elements than the
    /// entry function has witnesses (a malformed or crafted artifact).
    fn check_abi(&self) -> Result<(), String> {
        match self.flatten_params() {
            Err(AbiError::TooLarge) => Err(format!(
                "abi: parameters flatten to more than the entry function's {} parameter witnesses",
                self.entry_param_count()
            )),
            _ => Ok(()),
        }
    }

    /// Entry-point parameters flattened in ABI order. The compiler assigns
    /// them witnesses 0, 1, 2, ... in this order. Returns an empty list if
    /// the ABI cannot be read or its size does not match the entry
    /// function's parameter count.
    pub fn entry_params(&self) -> Vec<EntryParam> {
        match self.flatten_params() {
            Ok(out) if out.len() == self.entry_param_count() => out,
            _ => Vec::new(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::Write;

    fn deflate_b64(data: &[u8]) -> String {
        let mut e = flate2::write::DeflateEncoder::new(Vec::new(), flate2::Compression::default());
        e.write_all(data).unwrap();
        base64::engine::general_purpose::STANDARD.encode(e.finish().unwrap())
    }

    #[test]
    fn debug_symbols_decompression_is_capped() {
        let json = br#"{"debug_infos":[{"location_tree":{"locations":[]}}]}"#;
        let enc = deflate_b64(json);
        assert_eq!(decode_debug_symbols_capped(&enc, 1024).unwrap().len(), 1);
        let err = decode_debug_symbols_capped(&enc, 10).unwrap_err();
        assert!(err.contains("more than 10 bytes"), "{err}");
    }

    #[test]
    fn bytecode_decompression_is_capped() {
        let mut e = flate2::write::GzEncoder::new(Vec::new(), flate2::Compression::default());
        e.write_all(&[0u8; 4096]).unwrap();
        let enc = base64::engine::general_purpose::STANDARD.encode(e.finish().unwrap());
        let err = decode_bytecode_capped(&enc, 100).err().unwrap();
        assert!(err.contains("more than 100 bytes"), "{err}");
    }
}
