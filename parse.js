
// The raw source text of a def (its lines joined with \n, no trailing \n).
function defRaw(lines, i, next) {
  let s = "";
  for (let k = i; k < next; k++) s += (k > i ? "\n" : "") + lines[k].s;
  return s;
}

// ---- main block loop ------------------------------------------------------
// Appends tokens to `toks`. Returns {next, blankSep} where blankSep is true
// when two blocks in this range are separated by a blank line.
function parseBlocks(lines, start, end, refs, top, toks, mergeFirst) {
  let i = start, blankSep = false, prevBlock = false;
  let merge = mergeFirst;
  // Once a def is RECORDED (not merged into the paragraph), subsequent defs
  // are also recorded, never merged -- even with no blank line between
  // them. A def merges into a paragraph only when it directly follows it
  // and no def has been recorded since that paragraph was parsed.
  let defRecorded = false;
  while (i < end) {
    let j = i;
    while (j < end && isBlank(lines[j])) j++;
    if (j >= end) break;
    if (prevBlock && j > i) blankSep = true;
    const hadBlank = j > i;
    i = j;
    const L = lines[i];
    const code = tryCode(lines, i, end);
    if (code) {
      const prev = toks[toks.length - 1];
      if (!hadBlank && prev && (prev.t === "p" || prev.t === "x")) prev.text += "\n" + code.text;
      else toks.push({ t: "c", text: code.text, lang: "", fenced: false });
      i = code.next; prevBlock = true; continue;
    }
    const fence = tryFence(lines, i, end);
    if (fence) {
      toks.push({ t: "c", text: fence.text, lang: fence.lang, fenced: true });
      i = fence.next; prevBlock = true; continue;
    }
    const hd = tryHeading(lines, i);
    if (hd) {
      toks.push({ t: "h", depth: hd.depth, text: hd.text });
      i++; prevBlock = true; continue;
    }
    if (hrInfo(L)) {
      toks.push({ t: "hr" });
      i++; prevBlock = true; continue;
    }
    const bq = tryBlockquote(lines, i, end, refs);
    if (bq) {
      toks.push({ t: "bq", toks: bq.toks, raw: bq.raw });
      i = bq.next; prevBlock = true; continue;
    }
    const list = tryList(lines, i, end, refs);
    if (list) {
      toks.push({ t: "list", ordered: list.ordered, start: list.start, loose: list.loose, items: list.items, raw: list.raw });
      i = list.next; prevBlock = true; continue;
    }
    const html = tryHtml(lines, i, end);
    if (html) {
      toks.push({ t: "html", text: html.text });
      i = html.next; prevBlock = true; continue;
    }
    const def = tryDef(lines, i, end);
    if (def) {
      const prev = toks[toks.length - 1];
      if (!hadBlank && !defRecorded && prev && (prev.t === "p" || prev.t === "x")) prev.text += "\n" + defRaw(lines, i, def.next);
      else {
        if (!Object.prototype.hasOwnProperty.call(refs, def.tag)) refs[def.tag] = { href: def.href, title: def.title };
        defRecorded = true;
      }
      i = def.next; prevBlock = true; continue;
    }
    const table = tryTable(lines, i, end, refs);
    if (table) {
      toks.push({ t: "table", head: table.head, aligns: table.aligns, rows: table.rows });
      i = table.next; prevBlock = true; continue;
    }
    const lh = tryLheading(lines, i, end);
    if (lh) {
      toks.push({ t: "h", depth: lh.depth, text: lh.text });
      i = lh.next; prevBlock = true; continue;
    }
    if (top) {
      const para = collectParagraph(lines, i, end);
      const prev = toks[toks.length - 1];
      if (merge && prev && prev.t === "p") prev.text += "\n" + para.text;
      else toks.push({ t: "p", text: para.text });
      merge = false;
      defRecorded = false;
      i = para.next; prevBlock = true; continue;
    }
    const prev = toks[toks.length - 1];
    if (!hadBlank && prev && prev.t === "x") prev.text += "\n" + L.s;
    else { toks.push({ t: "x", text: L.s }); defRecorded = false; }
    i++; prevBlock = true;
  }
  return { next: i, blankSep };
}

// ---- inline parsing -------------------------------------------------------
// Inline state persists across the inline strings of one parse() call;
// inRawBlock is reset to false before each inline string (marked's lex()).
const INLINE_STATE = { inLink: false, inRawBlock: false, linkEmitted: false, linkParenPossible: true };
function resetInlineState() {
  INLINE_STATE.inLink = false;
  INLINE_STATE.inRawBlock = false;
  INLINE_STATE.linkEmitted = false;
  INLINE_STATE.linkParenPossible = true;
}
// ASCII punctuation test (for backslash escapes and masking).
function isPunctCh(c) {
  return (c >= 33 && c <= 47) || (c >= 58 && c <= 64) || (c >= 91 && c <= 96) || (c >= 123 && c <= 126);
}
// Find the matching ] for a [ at position i (accounting for nested brackets,
// backslash escapes and code spans). Returns the index of ] or -1.
function findLabelEnd(src, i) {
  let depth = 0;
  for (let j = i; j < src.length; j++) {
    const c = src[j];
    if (c === "\\" && j + 1 < src.length) { j++; continue; }
    if (c === "`") {
      let k = j, run = 0;
      while (k < src.length && src[k] === "`") { k++; run++; }
      // Special case (marked's label pattern): 2+ backticks immediately
      // before the closing ] are literal label content; skip them as
      // content and let the ] be handled by the normal bracket logic.
      if (run >= 2 && src[k] === "]") { j = k - 1; continue; }
      // Otherwise the backtick run must open a code span: find ANY later
      // backtick run as its closer (marked's label regex allows any
      // closer length). No closer at all -> the label is invalid.
      let m = k, found = -1;
      while (m < src.length) {
        if (src[m] === "`") { found = m; break; }
        m++;
      }
      if (found < 0) return -1;
      let q = found, r2 = 0;
      while (q < src.length && src[q] === "`") { q++; r2++; }
      j = found + r2 - 1;
      continue;
    }
    if (c === "[") depth++;
    else if (c === "]") {
      depth--;
      if (depth === 0) return j;
    }
  }
  return -1;
}
// Masked source for emStrong/del: same length as src, with delimiter runs
// inside code spans, link labels and html tags replaced so they cannot act
// as closers. Code spans / labels / tags become [aaa...] (punct boundaries
// Batched version: plain-text runs are appended in one slice instead of
// one char at a time; only masked segments are built separately.
function maskInline(src, refs) {
  let out = "";
  let i = 0;
  const n = src.length;
  let segStart = 0;
  const flushPlain = (upto) => { if (upto > segStart) { out += src.slice(segStart, upto); } };
  while (i < n) {
    const c = src[i];
    if (c === "\\" && i + 1 < n && isPunctCh(src.charCodeAt(i + 1))) { flushPlain(i); out += "++"; i += 2; segStart = i; continue; }
    if (c === "`") {
      let j = i, run = 0;
      while (j < n && src[j] === "`") { j++; run++; }
      let k = j, found = -1;
      while (k < n) {
        if (src[k] === "`") {
          let m = k, r2 = 0;
          while (m < n && src[m] === "`") { m++; r2++; }
          if (r2 === run) { found = k; break; }
          k = m;
        } else k++;
      }
      if (found >= 0) {
        const len = found + run - i;
        flushPlain(i);
        out += "[" + "a".repeat(Math.max(0, len - 2)) + "]";
        i = found + run;
        segStart = i;
        continue;
      }
      i = j; continue;
    }
    if (c === "<") {
      const m = /^<(?! )[^<>]*?>/.exec(src.slice(i));
      if (m) {
        flushPlain(i);
        out += "[" + "a".repeat(Math.max(0, m[0].length - 2)) + "]";
        i += m[0].length;
        segStart = i;
        continue;
      }
      i++; continue;
    }
    if (c === "[" || (c === "!" && src[i + 1] === "[")) {
      const start = c === "!" ? i + 1 : i;
      // Simple label end (no nesting): marked's blockSkip link pattern
      // forbids [ inside the label, so only the innermost [label](url)
      // is masked -- an outer [foo [bar](/u)](/u) is NOT masked as a
      // whole, which is what lets a * outside [baz](/uri) close an
      // emphasis (cm-519) while a * inside [bar*] stays hidden (cm-473).
      let close = -1;
      let j = start + 1;
      while (j < n) {
        const ch = src[j];
        if (ch === "\\" && j + 1 < n) { j += 2; continue; }
        if (ch === "`") {
          let k = j, run = 0;
          while (k < n && src[k] === "`") { k++; run++; }
          let m = k, found = -1;
          while (m < n) {
            if (src[m] === "`") {
              let q = m, r2 = 0;
              while (q < n && src[q] === "`") { q++; r2++; }
              if (r2 === run) { found = m; break; }
              m = q;
            } else m++;
          }
          // No equal-length closer: the label cannot match marked's
          // blockSkip link pattern (a lone backtick is neither [^\\[`]
          // nor a code span), so it is NOT masked.
          if (found < 0) { close = -1; break; }
          j = found + run; continue;
        }
        if (ch === "[") { close = -1; break; }
        if (ch === "]") { close = j; break; }
        j++;
      }
      if (close >= 0) {
        const after = src.slice(close + 1);
        // inline link [label](url): mask the label (blockSkip)
        let isLink = false;
        if (after.charCodeAt(0) === 40) isLink = true;
        else if (after.charCodeAt(0) === 91) {
          // [ref] : mask only if the ref resolves
          const close2 = findLabelEnd(src, close + 1);
          if (close2 >= 0) {
            const ref = src.slice(close + 2, close2);
            if (Object.prototype.hasOwnProperty.call(refs, normLabel(ref))) isLink = true;
          }
        } else {
          // shortcut: mask only if the label resolves
          const label = src.slice(start + 1, close);
          if (Object.prototype.hasOwnProperty.call(refs, normLabel(label))) isLink = true;
        }
        if (isLink) {
          const len = close - start + 1;
          flushPlain(i);
          out += (c === "!" ? "!" : "") + "[" + "a".repeat(Math.max(0, len - 2)) + "]";
          i = close + 1;
          segStart = i;
          continue;
        }
      }
      i++; continue;
    }
    i++;
  }
  flushPlain(n);
  return out;
}
// Last possible closer index for a delimiter run char in the masked source:
// the last index where a run of `ch` starts with a non-whitespace char before it.
function lastCloserIndex(masked, ch) {
  // Scan backward: the last closer is usually near the end, and we can
  // stop at the first valid run we meet.
  let s = masked.length - 1;
  while (s >= 0) {
    if (masked[s] !== ch) { s--; continue; }
    let start = s;
    while (start > 0 && masked[start - 1] === ch) start--;
    const prev = start === 0 ? "\n" : masked[start - 1];
    if (prev !== " " && prev !== "\t" && prev !== "\n" && prev !== "\r" && prev !== "\f") return start;
    s = start - 1;
  }
  return -1;
}

// ---- inline link parsing --------------------------------------------------
// Parse an inline link/image starting at e[0] ('[' or '!['). Returns
// {href, title, text, isImage, rawLen} or null.
function parseInlineLink(e) {
  const isImage = e.charCodeAt(0) === 33; // !
  let p = isImage ? 1 : 0;
  if (e.charCodeAt(p) !== CC_LBRACKET) return null;
  const labelEnd = findLabelEnd(e, p);
  if (labelEnd < 0) return null;
  const label = e.slice(p + 1, labelEnd);
  const labelOff = isImage ? 2 : 1;
  // Be(): reject when the label contains a tag/autolink extending past it
  if (labelHasTagBeyond(e, label, labelOff)) return null;
  p = labelEnd + 1;
  if (e.charCodeAt(p) !== 40) return null; // (
  p++;
  // skip [ \t\n]*
  while (p < e.length && (e.charCodeAt(p) === CC_SPACE || e.charCodeAt(p) === CC_TAB || e.charCodeAt(p) === CC_NL)) p++;
  const hrefStart = p;
  let href = "", title = "", rawLen = 0, angle = false;
  if (e.charCodeAt(p) === CC_LT) {
    // <(?:\\.|[^\n<>\\])+>
    let q = p + 1;
    while (q < e.length) {
      const c = e.charCodeAt(q);
      if (c === CC_BACKSLASH && q + 1 < e.length) { q += 2; continue; }
      if (c === CC_GT) break;
      if (c === CC_NL || c === CC_LT) return null;
      q++;
    }
    if (q >= e.length || e.charCodeAt(q) !== CC_GT) return null;
    href = e.slice(p + 1, q);
    p = q + 1;
    angle = true;
    // angle-bracket check: the href must not end with an odd number of
    // backslashes before the >
    const s = "<" + href + ">";
    const l = trimTrailBackslash(s.slice(0, -1));
    if ((s.length - l.length) % 2 === 0) return null;
  } else if (e.charCodeAt(p) === 41) {
    href = "";
  } else {
    // maximal non-space run
    let q = p;
    while (q < e.length) {
      const c = e.charCodeAt(q);
      if (c === CC_SPACE || c === CC_TAB || c === CC_NL || c < 32) break;
      q++;
    }
    if (q === p) return null;
    const R = e.slice(p, q);
    const k = keParen(R);
    if (k === -2) return null;
    if (k > -1) {
      href = R.slice(0, k);
      rawLen = hrefStart + k + 1;
      title = "";
      // trailing-backslash check on the whole match (raw ends with ))
      const rawSoFar = e.slice(0, rawLen);
      const r = trimTrailBackslash(rawSoFar.slice(0, -1));
      if ((rawSoFar.length - r.length) % 2 === 0) return null;
      return { href, title, text: label, isImage, rawLen, labelOff: isImage ? 2 : 1 };
    }
    href = R;
    p = q;
  }
  // optional title, then [ \t\n]* )
  {
    let q = p;
    let t = null;
    // title separator: (?:[ \t]+(?:\n[ \t]*)?|\n[ \t]*)
    let r = q, sep = false;
    if (r < e.length && (e.charCodeAt(r) === CC_SPACE || e.charCodeAt(r) === CC_TAB)) {
      while (r < e.length && (e.charCodeAt(r) === CC_SPACE || e.charCodeAt(r) === CC_TAB)) r++;
      sep = true;
      if (r < e.length && e.charCodeAt(r) === CC_NL) {
        r++;
        while (r < e.length && (e.charCodeAt(r) === CC_SPACE || e.charCodeAt(r) === CC_TAB)) r++;
      }
    } else if (r < e.length && e.charCodeAt(r) === CC_NL) {
      r++;
      while (r < e.length && (e.charCodeAt(r) === CC_SPACE || e.charCodeAt(r) === CC_TAB)) r++;
      sep = true;
    }
    if (sep && r < e.length) {
      const qc = e.charCodeAt(r);
      if (qc === CC_DQUOTE || qc === 39 || qc === 40) {
        const tt = scanTitle(e, r);
        if (tt !== null) { t = tt.text; q = tt.end; }
      }
    }
    if (t !== null) { title = t; p = q; }
    while (p < e.length && (e.charCodeAt(p) === CC_SPACE || e.charCodeAt(p) === CC_TAB || e.charCodeAt(p) === CC_NL)) p++;
    if (p >= e.length || e.charCodeAt(p) !== 41) return null;
    rawLen = p + 1;
  }
  // trailing-backslash check on the whole match
  {
    const rawSoFar = e.slice(0, rawLen);
    const r = trimTrailBackslash(rawSoFar.slice(0, -1));
    if ((rawSoFar.length - r.length) % 2 === 0) return null;
  }
  return { href, title, text: label, isImage, rawLen, labelOff, angle };
}
// Strip trailing backslashes from a string (L(s, "\\")).
function trimTrailBackslash(s) {
  let n = s.length;
  while (n > 0 && s.charCodeAt(n - 1) === CC_BACKSLASH) n--;
  return s.slice(0, n);
}
// Be(): does the label contain a < that starts a tag/autolink extending
// beyond the label? `src` is the full inline source, `label` the label text,
// `off` the label's offset in src.
function labelHasTagBeyond(src, label, off) {
  if (!label.includes("<")) return false;
  for (let s = 0; s < label.length; s++) {
    if (label[s] === "\\") { s++; continue; }
    if (label[s] === "`") {
      const m = /^(`+)([^`]|[^`][\s\S]*?[^`])\1(?!`)/.exec(label.slice(s));
      if (m) { s += m[0].length - 1; continue; }
    }
    if (label[s] !== "<") continue;
    const r = src.slice(off + s);
    const o = parseInlineTag(r) || parseAutolink(r);
    if (o) {
      if (o.rawLen > label.length - s) return true;
      s += o.rawLen - 1;
    }
  }
  return false;
}

// ---- inline tag / autolink / url / codespan / br / reflink ----------------
// Parse an inline HTML tag starting at e[0] ('<'). Returns {rawLen} or null.
function parseInlineTag(e) {
  if (e.charCodeAt(0) !== CC_LT) return null;
  // comment: <!--> and <!---> are abruptly-closed comments (just those
  // chars); a normal comment runs to the next -->
  if (e.startsWith("<!--")) {
    if (e.startsWith("<!-->")) return { rawLen: 5 };
    if (e.startsWith("<!--->")) return { rawLen: 7 };
    const idx = e.indexOf("-->", 4);
    if (idx >= 0) return { rawLen: idx + 3 };
    return { rawLen: e.length };
  }
  // processing instruction
  if (e.startsWith("<?")) {
    const idx = e.indexOf("?>", 2);
    if (idx >= 0) return { rawLen: idx + 2 };
    return null;
  }
  // declaration
  if (e.startsWith("<!") && e.length > 2 && ((e.charCodeAt(2) >= 65 && e.charCodeAt(2) <= 90) || (e.charCodeAt(2) >= 97 && e.charCodeAt(2) <= 122))) {
    const idx = e.indexOf(">", 2);
    if (idx >= 0) return { rawLen: idx + 1 };
    return null;
  }
  // CDATA
  if (e.startsWith("<![CDATA[")) {
    const idx = e.indexOf("]]>", 9);
    if (idx >= 0) return { rawLen: idx + 3 };
    return null;
  }
  // close tag: </name\s*>
  if (e.charCodeAt(1) === 47) {
    const m = /^<\/[a-zA-Z][a-zA-Z0-9-]*\s*>/.exec(e);
    if (m) return { rawLen: m[0].length };
    return null;
  }
  // open tag: <name (attr)* \s* /? >
  if (!((e.charCodeAt(1) >= 65 && e.charCodeAt(1) <= 90) || (e.charCodeAt(1) >= 97 && e.charCodeAt(1) <= 122))) return null;
  let p = 1;
  while (p < e.length) {
    const c = e.charCodeAt(p);
    if ((c >= 65 && c <= 90) || (c >= 97 && c <= 122) || (c >= 48 && c <= 57) || c === CC_DASH) p++;
    else break;
  }
  for (;;) {
    // skip whitespace; an attribute must be preceded by whitespace
    let q = p, hadWs = false;
    while (q < e.length && (e.charCodeAt(q) === CC_SPACE || e.charCodeAt(q) === CC_TAB || e.charCodeAt(q) === CC_NL || e.charCodeAt(q) === 13 || e.charCodeAt(q) === 12)) { q++; hadWs = true; }
    if (q >= e.length) return null;
    const c = e.charCodeAt(q);
    if (c === CC_GT) return { rawLen: q + 1 };
    if (c === 47 && e.charCodeAt(q + 1) === CC_GT) return { rawLen: q + 2 };
    if (!hadWs) return null;
    // attribute name
    if (!((c >= 65 && c <= 90) || (c >= 97 && c <= 122) || c === 95 || c === CC_COLON)) return null;
    p = q;
    while (p < e.length) {
      const ch = e.charCodeAt(p);
      if ((ch >= 65 && ch <= 90) || (ch >= 97 && ch <= 122) || (ch >= 48 && ch <= 57) || ch === 95 || ch === CC_COLON || ch === 46 || ch === CC_DASH) p++;
      else break;
    }
    // optional = value; if there is no =, leave p right after the name so
    // the whitespace stays for the next attribute's hadWs check
    let d = p;
    while (d < e.length && (e.charCodeAt(d) === CC_SPACE || e.charCodeAt(d) === CC_TAB || e.charCodeAt(d) === CC_NL || e.charCodeAt(d) === 13 || e.charCodeAt(d) === 12)) d++;
    if (d < e.length && e.charCodeAt(d) === CC_EQ) {
      d++;
      while (d < e.length && (e.charCodeAt(d) === CC_SPACE || e.charCodeAt(d) === CC_TAB || e.charCodeAt(d) === CC_NL || e.charCodeAt(d) === 13 || e.charCodeAt(d) === 12)) d++;
      if (d < e.length && e.charCodeAt(d) === CC_DQUOTE) {
        const close = e.indexOf('"', d + 1);
        if (close < 0) return null;
        d = close + 1;
      } else if (d < e.length && e.charCodeAt(d) === 39) {
        const close = e.indexOf("'", d + 1);
        if (close < 0) return null;
        d = close + 1;
      } else {
        const startVal = d;
        while (d < e.length) {
          const ch = e.charCodeAt(d);
          if (ch === CC_SPACE || ch === CC_TAB || ch === CC_NL || ch === 13 || ch === 12 || ch === CC_DQUOTE || ch === 39 || ch === CC_EQ || ch === CC_LT || ch === CC_GT || ch === CC_BACKTICK) break;
          d++;
        }
        if (d === startVal) return null;
      }
      p = d;
    }
  }
}
// Parse an angle-bracket autolink <scheme:...> or <email>. Returns {text, href, rawLen} or null.
function parseAutolink(e) {
  if (e.charCodeAt(0) !== CC_LT) return null;
  const m = /^<([a-zA-Z][a-zA-Z0-9+.-]{1,31}:[^\s\x00-\x1f<>]*|[a-zA-Z0-9.!#$%&'*+/=?^_`{|}~-]+@[a-zA-Z0-9](?:[a-zA-Z0-9-]{0,61}[a-zA-Z0-9])?(?:\.[a-zA-Z0-9](?:[a-zA-Z0-9-]{0,61}[a-zA-Z0-9])?)+)>/.exec(e);
  if (!m) return null;
  const text = m[1];
  const href = /^[a-zA-Z][a-zA-Z0-9+.-]{1,31}:/.test(text) ? text : "mailto:" + text;
  return { text, href, rawLen: m[0].length };
}
// Trim trailing punctuation from an extended autolink URL (_backpedal).
function backpedalUrl(u) {
  // repeatedly strip a trailing run of [?!.,:;*_'\"~)] (and & not starting an entity)
  for (;;) {
    const m = /^(?:[^?!.,:;*_'\"~()&]+|\([^)]*\)|&(?![a-zA-Z0-9]+;$)|[?!.,:;*_'\"~)]+(?!$))+/.exec(u);
    const next = m ? m[0] : "";
    if (next === u) return u;
    u = next;
  }
}
// Parse an extended autolink (bare URL, www., email, mailto:/xmpp:).
// Returns {text, href, rawLen} or null.
// The regexes are precompiled at module load (building them per call was
// a top hotspot).
const _EMAIL_PAT = "[a-zA-Z0-9._+-]+@[a-zA-Z0-9-_]+(?:\\.[a-zA-Z0-9-_]*[a-zA-Z0-9])+(?![\\w-])";
const _MAILTO_RE = new RegExp("^(?:mailto:" + _EMAIL_PAT + "|xmpp:" + _EMAIL_PAT + "(?:\\/[a-zA-Z0-9@.]+)?)");
const _PROTO_RE = /^((?:[hH][tT][tT][pP][sS]?|[fF][tT][pP]):\/\/|www\.)(?:[a-zA-Z0-9\-]+\.?)+[^\s<]*/;
const _BARE_EMAIL_RE = new RegExp("^" + _EMAIL_PAT);
function parseUrl(e) {
  // emailProtocol: mailto:email | xmpp:email[/...]
  let m = _MAILTO_RE.exec(e);
  if (m) return { text: m[0], href: m[0], rawLen: m[0].length };
  // protocol:// or www.
  m = _PROTO_RE.exec(e);
  if (m) {
    let text = backpedalUrl(m[0]);
    const href = m[1] === "www." ? "http://" + text : text;
    return { text, href, rawLen: text.length };
  }
  // bare email: only run the (backtracking) regex when the leading
  // email-char run is actually followed by @.
  let j = 0;
  while (j < e.length && isEmailCh(e.charCodeAt(j))) j++;
  if (j < e.length && e.charCodeAt(j) === 64) {
    m = _BARE_EMAIL_RE.exec(e);
    if (m) return { text: m[0], href: "mailto:" + m[0], rawLen: m[0].length };
  }
  return null;
}
// Parse a code span starting at e[0] ('`'). Returns {text, rawLen} or null.
function parseCodespan(e) {
  const m = /^(`+)([^`]|[^`][\s\S]*?[^`])\1(?!`)/.exec(e);
  if (!m) return null;
  let text = m[2].replace(/\n/g, " ");
  if (/[^ ]/.test(text) && text.charCodeAt(0) === CC_SPACE && text.charCodeAt(text.length - 1) === CC_SPACE) {
    text = text.substring(1, text.length - 1);
  }
  return { text, rawLen: m[0].length };
}
// Parse a hard break: 2+ spaces + \n, or a single backslash + \n.
// The \n must not be followed by only whitespace to end of input
// (a trailing backslash at EOF is literal). Trailing spaces/tabs after
// the newline are consumed as part of the break.
function parseBr(e) {
  let i = 0;
  while (i < e.length && e.charCodeAt(i) === CC_SPACE) i++;
  let isBr = false;
  if (i >= 2 && e.charCodeAt(i) === CC_NL) isBr = true;
  else if (i === 0 && e.charCodeAt(0) === CC_BACKSLASH && e.charCodeAt(1) === CC_NL) { i = 1; isBr = true; }
  if (!isBr) return null;
  const nl = i;
  let k = nl + 1;
  while (k < e.length) {
    const c = e.charCodeAt(k);
    if (c === CC_SPACE || c === CC_TAB || c === CC_NL || c === CC_CR || c === 12 || c === 11) k++;
    else break;
  }
  if (k >= e.length) return null;
  let j = nl + 1;
  while (j < e.length && (e.charCodeAt(j) === CC_SPACE || e.charCodeAt(j) === CC_TAB)) j++;
  return { rawLen: j };
}
// Parse a reference link [label][ref] / [label][] / [label]. Returns
// {href, title, text, isImage, rawLen} or a text token {text, rawLen: 1} when
// the ref does not resolve (marked returns a text token of the first char).
function parseReflink(e, refs) {
  const isImage = e.charCodeAt(0) === 33;
  let p = isImage ? 1 : 0;
  if (e.charCodeAt(p) !== CC_LBRACKET) return null;
  const labelEnd = findLabelEnd(e, p);
  if (labelEnd < 0) return null;
  const label = e.slice(p + 1, labelEnd);
  const labelOff = isImage ? 2 : 1;
  if (labelHasTagBeyond(e, label, labelOff)) return null;
  let ref = null, rawLen = 0;
  // full reference form [label][ref] — the ref allows no nested brackets
  if (e.charCodeAt(labelEnd + 1) === CC_LBRACKET) {
    let q = labelEnd + 2;
    // lookahead (?!\s*\]): the ref must not be all-whitespace before ]
    let w = q;
    while (w < e.length && (e.charCodeAt(w) === CC_SPACE || e.charCodeAt(w) === CC_TAB || e.charCodeAt(w) === CC_NL)) w++;
    if (!(w < e.length && e.charCodeAt(w) === CC_RBRACKET)) {
      let ok = true;
      while (q < e.length && e.charCodeAt(q) !== CC_RBRACKET) {
        const c = e.charCodeAt(q);
        if (c === CC_BACKSLASH && q + 1 < e.length) { q += 2; continue; }
        if (c === CC_LBRACKET) { ok = false; break; }
        if (c === CC_NL) {
          let r = q + 1;
          while (r < e.length && (e.charCodeAt(r) === CC_SPACE || e.charCodeAt(r) === CC_TAB)) r++;
          if (r >= e.length || e.charCodeAt(r) === CC_NL) { ok = false; break; }
        }
        q++;
      }
      if (ok && q < e.length && e.charCodeAt(q) === CC_RBRACKET) {
        ref = e.slice(labelEnd + 2, q);
        rawLen = q + 1;
      }
    }
  }
  if (ref === null) {
    // collapsed [] or shortcut: ref = label
    if (e.charCodeAt(labelEnd + 1) === CC_LBRACKET && e.charCodeAt(labelEnd + 2) === CC_RBRACKET) {
      ref = label;
      rawLen = labelEnd + 3;
    } else {
      ref = label;
      rawLen = labelEnd + 1;
    }
  }
  const entry = refs[normLabel(ref)];
  if (!entry) {
    const ch = e.charAt(0);
    return { textOnly: ch, rawLen: 1 };
  }
  return { href: entry.href, title: entry.title || null, text: label, isImage, rawLen };
}

// ---- emphasis / strikethrough --------------------------------------------
// Unicode character classes used by the delimiter algorithms.
const RE_PUNCT = "[\\p{P}\\p{S}]";
const RE_PUNCT_NT = "(?!~)[\\p{P}\\p{S}]";
const RE_PUNCT_SPACE = "[\\s\\p{P}\\p{S}]";
const RE_PUNCT_SPACE_NT = "(?!~)[\\s\\p{P}\\p{S}]";
const RE_NOT_PS = "[^\\s\\p{P}\\p{S}]";
const RE_NOT_PS_T = "(?:[^\\s\\p{P}\\p{S}]|~)";
// Left-delimiter regex (GFM): run of * or _ followed by a punct char or a
// non-space char. Groups: 1 punct after *, 2 non-space after *, 3 punct
// after _, 4 non-space after _.
const EM_L_DELIM = new RegExp(
  "^(?:\\*+(?:((?!\\*)" + RE_PUNCT_NT + ")|([^\\s*]))?)|^_+(?:((?!_)" + RE_PUNCT_NT + ")|([^\\s_]))?", "u");
// Right-delimiter regexes (global). Groups 1-5 (1-6 for *) classify the
// closer run. The first alternative is the "kt" special case: for * it is
// ^[^_*]*?__[^_*]*?\*[^_*]*?(?=__), for _ it is the mirror image.
// NOTE: marked's closer regexes have NO notPunctSpace(X+)(?=notPunctSpace)
// alternative (group 6). For * we keep it: a * between two word chars CAN
// close (no intraword rule), and it is what makes *foo*bar work. For _ we
// OMIT it: a _ between two word chars can NOT close (intraword rule), so
// _foo_bar stays literal and _foo_bar_baz_ closes only at the final _.
function emRDelim(delim) {
  const esc = delim === "*" ? "\\*" : "_";
  const notPS = delim === "*" ? RE_NOT_PS_T : RE_NOT_PS;
  const ps = delim === "*" ? RE_PUNCT_SPACE_NT : RE_PUNCT_SPACE;
  const punct = delim === "*" ? RE_PUNCT_NT : RE_PUNCT;
  const first = delim === "*"
    ? "^[^_*]*?__[^_*]*?\\*[^_*]*?(?=__)|"
    : "^[^_*]*?\\*\\*[^_*]*?_[^_*]*?(?=\\*\\*)|";
  let src =
    first +
    "[^" + esc + "]+(?=[^" + esc + "])|" +
    "(?!" + esc + ")" + punct + "(" + esc + "+)(?=[\\s]|$)|" +
    notPS + "(" + esc + "+)(?!" + esc + ")(?=" + ps + "|$)|" +
    "(?!" + esc + ")" + ps + "(" + esc + "+)(?=" + notPS + ")|" +
    "[\\s](" + esc + "+)(?!" + esc + ")(?=" + punct + ")|" +
    "(?!" + esc + ")" + punct + "(" + esc + "+)(?!" + esc + ")(?=" + punct + ")";
  if (delim === "*") src += "|" + notPS + "(" + esc + "+)(?=" + notPS + ")";
  return new RegExp(src, "gu");
}
const EM_R_AST = emRDelim("*");
const EM_R_UND = emRDelim("_");
// Delimiter right regex for ~ (same shape, ~ runs).
const DEL_R = new RegExp(
  "^[^~]+(?=[^~])|(?!~)" + RE_PUNCT + "(~~?)(?=[\\s]|$)|" +
  RE_NOT_PS + "(~~?)(?!~)(?=" + RE_PUNCT_SPACE + "|$)|" +
  "(?!~)" + RE_PUNCT_SPACE + "(~~?)(?=" + RE_NOT_PS + ")|" +
  "[\\s](~~?)(?!~)(?=" + RE_PUNCT + ")|" +
  "(?!~)" + RE_PUNCT + "(~~?)(?!~)(?=" + RE_PUNCT + ")|" +
  RE_NOT_PS + "(~~?)(?=" + RE_NOT_PS + ")", "gu");
const DEL_L = new RegExp("^(~~?)(?:((?!~)" + RE_PUNCT + ")|[^\\s~])", "u");
// Is this string (a single code point) punctuation/whitespace/symbol?
const RE_IS_PUNCT_SPACE = new RegExp("^" + RE_PUNCT_SPACE + "$", "u");
// Same, but excluding * and _ (marked's `punctuation` rule used for the
// can-open checks).
const RE_IS_PUNCT_NO_DELIM = /^(?![*_])[\s\p{P}\p{S}]$/u;
const RE_IS_ALNUM = /^[\p{L}\p{N}]$/u;
// The code point ending at index i in s (handles a surrogate pair).
function codePointBefore(s, i) {
  if (i <= 0) return "";
  const lo = s.charCodeAt(i - 1);
  if (lo >= 0xDC00 && lo <= 0xDFFF && i >= 2) {
    const hi = s.charCodeAt(i - 2);
    if (hi >= 0xD800 && hi <= 0xDBFF) return s.slice(i - 2, i);
  }
  return s[i - 1];
}
// Try emphasis/strong at the start of e. `masked` is the full masked source,
// `off` is e's offset in it, `prevLast` the previous token's last char.
// Returns {type, raw, text} or null.
function tryEmStrong(e, masked, off, prevLast) {
  const s = EM_L_DELIM.exec(e);
  if (!s || (!s[1] && !s[2] && !s[3] && !s[4])) return null;
  const r = s[0][0];
  const o = prevLast === r;
  const i = off;
  let l = i;
  while (l > 0 && masked[l - 1] === r) l--;
  const p = codePointBefore(masked, l);
  const h = p === "*" || p === "_" || (p !== "" && RE_IS_PUNCT_NO_DELIM.test(p));
  let n = prevLast;
  if (l < i) n = p;
  const u = l < i ? h : (n !== "" && RE_IS_PUNCT_NO_DELIM.test(n));
  if (s[4] && n !== "" && RE_IS_ALNUM.test(n)) return null;
  const d = s[1] || s[3] || "";
  if (!d || !n || u) {
    const k = [...s[0]].length - 1;
    let m = k, f = 0;
    const y = i - l + k;
    const R = p.trim() !== "" && (!!d || (r === "*" && !h));
    const A = r === "*" ? EM_R_AST : EM_R_UND;
    const v = lastCloserIndex(masked, r);
    const Q = i + k;
    if (v < Q) return null;
    const t = masked.slice(i + k);
    const ee = v - Q;
    A.lastIndex = 0;
    let m2;
    while ((m2 = A.exec(t)) !== null && !(m2.index > ee)) {
      const g = m2[1] || m2[2] || m2[3] || m2[4] || m2[5] || m2[6];
      if (!g) continue;
      const b = [...g].length;
      if (m2[3] || m2[4]) { m += b; continue; }
      else if (m2[5] || m2[6] || R) {
        if (o && (m2[5] || m2[6])) break;
        if (y % 3 && !((y + b) % 3)) { f += b; continue; }
      }
      m -= b;
      if (m > 0) continue;
      const bb = Math.min(b, b + m + f);
      const te = [...m2[0]][0].length;
      const M = e.slice(0, k + m2.index + te + bb);
      if (Math.min(k, bb) % 2) {
        return { type: "em", raw: M, text: M.slice(1, -1) };
      }
      return { type: "strong", raw: M, text: M.slice(2, -2) };
    }
  }
  return null;
}
// Try strikethrough at the start of e. Returns {type, raw, text} or null.
function tryDel(e, masked, off, prevLast) {
  const s = DEL_L.exec(e);
  if (!s) return null;
  const n = prevLast;
  // can-open: (no punct after the run) || (n empty) || (n is punct/space)
  if (!((s[1] || "") === "" || n === "" || RE_IS_PUNCT_NO_DELIM.test(n))) return null;
  const o = [...s[0]].length - 1;
  let p = o;
  const u = lastCloserIndex(masked, "~");
  const d = off + o;
  if (u < d) return null;
  const t = masked.slice(off + o);
  const k = u - d;
  DEL_R.lastIndex = 0;
  let m2;
  while ((m2 = DEL_R.exec(t)) !== null && !(m2.index > k)) {
    const g = m2[1] || m2[2] || m2[3] || m2[4] || m2[5] || m2[6];
    if (!g) continue;
    const l = [...g].length;
    if (l !== o) continue;
    if (m2[3] || m2[4]) { p += l; continue; }
    p -= l;
    if (p > 0) continue;
    const ll = Math.min(l, l + p);
    const te = [...m2[0]][0].length;
    const b = e.slice(0, o + m2.index + te + ll);
    return { type: "del", raw: b, text: b.slice(o, -o) };
  }
  return null;
}

// ---- inline text run ------------------------------------------------------
// Email chars (for the text-run stop conditions and url detection).
// Lookup tables (indexed by char code) replace per-char comparison chains
// in the hot text-run loop.
const _EMAIL_TBL = new Uint8Array(128);
for (const c of [46, 33, 35, 36, 37, 38, 39, 42, 43, 47, 61, 63, 94, 95, 96, 123, 124, 125, 126, 45]) _EMAIL_TBL[c] = 1;
for (let c = 48; c <= 57; c++) _EMAIL_TBL[c] = 1;
for (let c = 65; c <= 90; c++) _EMAIL_TBL[c] = 1;
for (let c = 97; c <= 122; c++) _EMAIL_TBL[c] = 1;
const _ALNUM_TBL = new Uint8Array(128);
for (let c = 48; c <= 57; c++) _ALNUM_TBL[c] = 1;
for (let c = 65; c <= 90; c++) _ALNUM_TBL[c] = 1;
for (let c = 97; c <= 122; c++) _ALNUM_TBL[c] = 1;
// Chars that stop a text run: \ < ! [ ` * ~ _
const _TEXT_STOP_TBL = new Uint8Array(128);
for (const c of [92, 60, 33, 91, 96, 42, 126, 95]) _TEXT_STOP_TBL[c] = 1;
function isEmailCh(c) { return c < 128 && _EMAIL_TBL[c] === 1; }
function isAlnumCh(c) { return c < 128 && _ALNUM_TBL[c] === 1; }
// Length of the text run starting at e[0]. Stops before a special char, a
// protocol://, www., an email start, mailto:/xmpp:, a hard break, or EOL.
// Hot path: uses char-code checks, no regexes and no string slices.
function textRunLen(e) {
  const n = e.length;
  if (n === 0) return 0;
  let i = 0;
  // first unit: a backtick run, a ~ run, or one char
  if (e.charCodeAt(0) === CC_BACKTICK) {
    while (i < n && e.charCodeAt(i) === CC_BACKTICK) i++;
  } else if (e.charCodeAt(0) === 126) {
    while (i < n && e.charCodeAt(i) === 126) i++;
  } else {
    i = 1;
  }
  while (i < n) {
    const c = e.charCodeAt(i);
    if (c < 128 && _TEXT_STOP_TBL[c] === 1) break;
    // protocol:// (http://, https://, ftp://, case-insensitive)
    if (c === 104 || c === 72 || c === 102 || c === 70) {
      const c1 = e.charCodeAt(i + 1) | 32, c2 = e.charCodeAt(i + 2) | 32, c3 = e.charCodeAt(i + 3) | 32;
      if (c === 104 || c === 72) {
        if (c1 === 116 && c2 === 116 && c3 === 112) {
          let k = i + 4;
          if ((e.charCodeAt(k) | 32) === 115) k++;
          if (e.charCodeAt(k) === 58 && e.charCodeAt(k + 1) === 47 && e.charCodeAt(k + 2) === 47) break;
        }
      } else if (c1 === 116 && c2 === 112) {
        const k = i + 3;
        if (e.charCodeAt(k) === 58 && e.charCodeAt(k + 1) === 47 && e.charCodeAt(k + 2) === 47) break;
      }
    }
    // www. (preceded by whitespace, *, _, ~, (, ] or start)
    if ((c === 119 || c === 87) && (e.charCodeAt(i + 1) | 32) === 119 && (e.charCodeAt(i + 2) | 32) === 119 && e.charCodeAt(i + 3) === 46) {
      const prev = e[i - 1];
      if (prev === " " || prev === "\t" || prev === "\n" || prev === "*" || prev === "_" || prev === "~" || prev === "(" || prev === "]") break;
    }
    // email start: an email-char run followed by @. Only scan at a word
    // boundary (previous char not an email char) -- inside a run the
    // email, if any, starts at the run's beginning, where we already
    // scanned (and parseUrl already ruled out an email at e[0]).
    if (isEmailCh(c) && !isEmailCh(e.charCodeAt(i - 1))) {
      let j = i;
      while (j < n && isEmailCh(e.charCodeAt(j))) j++;
      if (j < n && e.charCodeAt(j) === 64) break;
    }
    // mailto:/xmpp: after a non-alphanumeric char: consume the char, stop.
    // Only run the regex when the next char could start mailto:/xmpp:.
    if (!isAlnumCh(c)) {
      const nc = e.charCodeAt(i + 1);
      if (nc === 109 || nc === 120) {
        const rest = e.slice(i + 1);
        if (/^(?:mailto|xmpp):[a-zA-Z0-9._+-]+@[a-zA-Z0-9-_]+(?:\.[a-zA-Z0-9-_]*[a-zA-Z0-9])+(?![\w-])/.test(rest)) {
          i++;
          break;
        }
      }
    }
    // hard break: 2+ spaces + \n starting here (stop before the spaces,
    // so a text run that began at e.g. "!" does not swallow them).
    // Only count when there are actually 2+ spaces.
    if (c === CC_SPACE && e.charCodeAt(i + 1) === CC_SPACE) {
      let k = i;
      while (k < n && e.charCodeAt(k) === CC_SPACE) k++;
      if (k - i >= 2 && e.charCodeAt(k) === CC_NL) break;
    }
    // hard break: a non-space char followed by 2+ spaces + \n
    if (c !== CC_SPACE && c !== CC_TAB && e.charCodeAt(i + 1) === CC_SPACE && e.charCodeAt(i + 2) === CC_SPACE) {
      let k = i + 1;
      while (k < n && e.charCodeAt(k) === CC_SPACE) k++;
      if (k - (i + 1) >= 2 && e.charCodeAt(k) === CC_NL) { i++; break; }
    }
    i++;
  }
  return i;
}
// ---- De(): build a link/image token ---------------------------------------
// Returns the rendered HTML for the link/image, or null when a nested link
// was emitted inside the link text (the outer link is rejected).
function makeLink(link, refs, textMode) {
  const hrefRaw = unescapePunct(link.href || "");
  const titleRaw = link.title ? unescapePunct(link.title) : null;
  const label = (link.text || "").replace(/\\([\[\]])/g, "$1");
  const isImage = !!link.isImage;
  if (textMode) {
    // text renderer: a link/image renders as its text
    if (isImage) return inlineParse(label, refs, true);
    const p = INLINE_STATE.inLink, h = INLINE_STATE.linkEmitted, u = INLINE_STATE.inRawBlock;
    INLINE_STATE.inLink = true;
    INLINE_STATE.linkEmitted = false;
    const inner = inlineParse(label, refs, true);
    const k = INLINE_STATE.linkEmitted;
    INLINE_STATE.linkEmitted = h;
    INLINE_STATE.inLink = p;
    if (k) { INLINE_STATE.inRawBlock = u; return null; }
    INLINE_STATE.linkEmitted = true;
    return inner;
  }
  if (isImage) {
    // alt text: parse with the text renderer
    const alt = inlineParse(label, refs, true);
    const href = cleanUrl(hrefRaw);
    if (href === null) return escText(alt);
    let o = '<img src="' + escText(href) + '" alt="' + escText(alt) + '"';
    if (titleRaw) o += ' title="' + escText(titleRaw) + '"';
    return o + ">";
  }
  const p = INLINE_STATE.inLink, h = INLINE_STATE.linkEmitted, u = INLINE_STATE.inRawBlock;
  INLINE_STATE.inLink = true;
  INLINE_STATE.linkEmitted = false;
  const inner = inlineParse(label, refs, false);
  const k = INLINE_STATE.linkEmitted;
  INLINE_STATE.linkEmitted = h;
  INLINE_STATE.inLink = p;
  if (k) {
    INLINE_STATE.inRawBlock = u;
    return null;
  }
  INLINE_STATE.linkEmitted = true;
  const href = cleanUrl(hrefRaw);
  if (href === null) return inner;
  let o = '<a href="' + escText(href) + '"';
  if (titleRaw) o += ' title="' + escText(titleRaw) + '"';
  return o + ">" + inner + "</a>";
}

// ---- main inline loop -----------------------------------------------------
// Renders an inline source to HTML (textMode=false) or to plain text
// (textMode=true, used for image alt text).
let INLINE_DEPTH = 0;
function inlineParse(src, refs, textMode) {
  const savedLinkParen = INLINE_STATE.linkParenPossible;
  INLINE_STATE.linkParenPossible = savedLinkParen && src.includes(")");
  // inRawBlock resets before each top-level inline string only (marked's
  // lex()); recursive calls (link text, emphasis) keep the outer value.
  if (INLINE_DEPTH === 0) INLINE_STATE.inRawBlock = false;
  INLINE_DEPTH++;
  const out = inlineParseInner(src, refs, textMode);
  INLINE_DEPTH--;
  INLINE_STATE.linkParenPossible = savedLinkParen;
  return out;
}
function inlineParseInner(src, refs, textMode) {
  const hasDelim = src.includes("*") || src.includes("_") || src.includes("~");
  // The mask only hides delimiters inside code spans, link labels, html
  // tags, and backslash escapes. If none of those can occur, the masked
  // source is the source itself -- skip building a copy.
  const masked = hasDelim && (src.includes("`") || src.includes("[") || src.includes("<") || src.includes("\\")) ? maskInline(src, refs) : src;
  let out = "";
  let e = src, off = 0;
  let prevLast = "", prevWasText = false;
  while (e.length > 0) {
    if (!prevWasText) prevLast = "";
    prevWasText = false;
    const c0 = e.charCodeAt(0);
    let consumed = 0;
    // escape
    if (c0 === CC_BACKSLASH && e.length > 1 && isPunctCh(e.charCodeAt(1))) {
      out += textMode ? e[1] : escText(e[1]);
      consumed = 2;
    }
    // tag
    if (consumed === 0 && c0 === CC_LT) {
      const tag = parseInlineTag(e);
      if (tag) {
        const t0 = e.slice(0, tag.rawLen);
        if (!INLINE_STATE.inLink && /^<a /i.test(t0)) INLINE_STATE.inLink = true;
        else if (INLINE_STATE.inLink && /^<\/a>/i.test(t0)) INLINE_STATE.inLink = false;
        if (!INLINE_STATE.inRawBlock && /^<(pre|code|kbd|script)(\s|>)/i.test(t0)) INLINE_STATE.inRawBlock = true;
        else if (INLINE_STATE.inRawBlock && /^<\/(pre|code|kbd|script)(\s|>)/i.test(t0)) INLINE_STATE.inRawBlock = false;
        out += t0;
        consumed = tag.rawLen;
      }
    }
    // link
    if (consumed === 0 && (c0 === CC_LBRACKET || (c0 === 33 && e.charCodeAt(1) === CC_LBRACKET)) && INLINE_STATE.linkParenPossible) {
      const link = parseInlineLink(e);
      if (link) {
        const html = makeLink(link, refs, textMode);
        if (html !== null) { out += html; consumed = link.rawLen; }
      }
    }
    // reflink
    if (consumed === 0 && (c0 === CC_LBRACKET || (c0 === 33 && e.charCodeAt(1) === CC_LBRACKET))) {
      const rl = parseReflink(e, refs);
      if (rl) {
        if (rl.textOnly !== undefined) {
          out += textMode ? rl.textOnly : escText(rl.textOnly);
          consumed = 1;
        } else {
          const html = makeLink(rl, refs, textMode);
          if (html !== null) { out += html; consumed = rl.rawLen; }
        }
      }
    }
    // emStrong
    if (consumed === 0 && (c0 === 42 || c0 === 95) && hasDelim) {
      const em = tryEmStrong(e, masked, off, prevLast);
      if (em) {
        const inner = inlineParse(em.text, refs, textMode);
        out += textMode ? inner : (em.type === "em" ? "<em>" + inner + "</em>" : "<strong>" + inner + "</strong>");
        consumed = em.raw.length;
      }
    }
    // codespan
    if (consumed === 0 && c0 === CC_BACKTICK) {
      const cs = parseCodespan(e);
      if (cs) {
        out += textMode ? cs.text : "<code>" + escFull(cs.text) + "</code>";
        consumed = cs.rawLen;
      }
    }
    // br
    if (consumed === 0 && (c0 === CC_SPACE || c0 === CC_BACKSLASH)) {
      const br = parseBr(e);
      if (br) {
        if (!textMode) out += "<br>";
        consumed = br.rawLen;
      }
    }
    // del
    if (consumed === 0 && c0 === 126 && hasDelim) {
      const d = tryDel(e, masked, off, prevLast);
      if (d) {
        const inner = inlineParse(d.text, refs, textMode);
        out += textMode ? inner : "<del>" + inner + "</del>";
        consumed = d.raw.length;
      }
    }
    // autolink
    if (consumed === 0 && c0 === CC_LT) {
      const al = parseAutolink(e);
      if (al) {
        const href = cleanUrl(al.href);
        if (href !== null) {
          out += textMode ? al.text : '<a href="' + escFull(href) + '">' + escFull(al.text) + "</a>";
          consumed = al.rawLen;
        }
      }
    }
    // url (extended autolink), only when not inside a link
    if (consumed === 0 && !INLINE_STATE.inLink) {
      const u = parseUrl(e);
      if (u) {
        const href = cleanUrl(u.href);
        if (href !== null) {
          out += textMode ? u.text : '<a href="' + escFull(href) + '">' + escFull(u.text) + "</a>";
          consumed = u.rawLen;
        }
      }
    }
    // inlineText
    if (consumed === 0) {
      const len = textRunLen(e);
      const raw = e.slice(0, len);
      const text = INLINE_STATE.inRawBlock ? raw : decodeEntities(raw);
      out += textMode ? text : escText(text);
      if (raw.length > 0 && raw.charCodeAt(raw.length - 1) !== 95) prevLast = raw[raw.length - 1];
      prevWasText = true;
      consumed = len;
    }
    e = e.slice(consumed);
    off += consumed;
  }
  return out;
}

// ---- char codes -----------------------------------------------------------
const CC_SPACE = 32, CC_TAB = 9, CC_NL = 10, CC_CR = 13, CC_BACKSLASH = 92,
  CC_BACKTICK = 96, CC_LT = 60, CC_GT = 62, CC_LBRACKET = 91, CC_RBRACKET = 93,
  CC_DQUOTE = 34, CC_DASH = 45, CC_COLON = 58, CC_EQ = 61, CC_HASH = 35,
  CC_TILDE = 126, CC_ASTERISK = 42, CC_UNDERSCORE = 95, CC_BANG = 33,
  CC_PIPE = 124, CC_SLASH = 47, CC_LPAREN = 40, CC_RPAREN = 41, CC_GT2 = 62;

// ---- text helpers (marked's P, Ie, he, F, anyPunctuation) ------------------
const ESC_MAP = { "&": "&amp;", "<": "&lt;", ">": "&gt;", '"': "&quot;", "'": "&#39;" };
const RE_ESC_TEST = /[&<>"']/;
const RE_ESC_REPLACE = /[&<>"']/g;
const RE_ESC_TEST_NO_ENCODE = /[<>"']|&(?!(#\d{1,7}|#[Xx][a-fA-F0-9]{1,6}|\w+);)/;
const RE_ESC_REPLACE_NO_ENCODE = /[<>"']|&(?!(#\d{1,7}|#[Xx][a-fA-F0-9]{1,6}|\w+);)/g;
// P(a, true): escape & always. P(a): escape & only when not a valid entity.
function escFull(s) { return RE_ESC_TEST.test(s) ? s.replace(RE_ESC_REPLACE, (c) => ESC_MAP[c]) : s; }
function escText(s) { return RE_ESC_TEST_NO_ENCODE.test(s) ? s.replace(RE_ESC_REPLACE_NO_ENCODE, (c) => ESC_MAP[c]) : s; }
const RE_NUM_REF = /&#(?:(\d{1,7})|[Xx]([A-Fa-f0-9]{1,6}));/;
const RE_NUM_REF_OR_AMP = /&#(?:(\d{1,7})|[Xx]([A-Fa-f0-9]{1,6}));|&(?!(#\d{1,7}|#[Xx][a-fA-F0-9]{1,6}|\w+);)/g;
// Ie: decode numeric character references; a bare & becomes &amp;.
function decodeEntities(s) {
  if (!RE_NUM_REF.test(s)) return s;
  return s.replace(RE_NUM_REF_OR_AMP, (m, t, n) => {
    if (t === undefined && n === undefined) return "&amp;";
    const v = t === undefined ? parseInt(n, 16) : parseInt(t, 10);
    if (v === 0 || v > 0x10FFFF || (v >= 0xD800 && v <= 0xDFFF)) return "\uFFFD";
    if (v === 38) return "&amp;";
    return String.fromCodePoint(v);
  });
}
// he: encodeURI + %25 -> %; null when encodeURI throws (lone surrogates).
function cleanUrl(s) {
  try { return encodeURI(s).replace(/%25/g, "%"); } catch { return null; }
}
// F: label normalization (trim, collapse whitespace, case-fold).
function normLabel(s) { return s.trim().replace(/\s+/g, " ").toLowerCase().toUpperCase().toLowerCase(); }
// anyPunctuation: \X -> X for ASCII punctuation X.
const RE_ANY_PUNCT = /\\([!"#$%&'()*+,\-.\/:;<=>?@\[\]\\^_`{|}~])/g;
function unescapePunct(s) { return s.replace(RE_ANY_PUNCT, "$1"); }
// Is this char code Unicode punctuation/symbol?
const RE_IS_PUNCT_CODE = /^[\p{P}\p{S}]$/u;
function isPunctCode(c) { return c !== "" && RE_IS_PUNCT_CODE.test(c); }
// L(a, e): trim trailing e's. L(a, e, true): trim trailing non-e's.
function trimEndChar(s, ch) { let n = s.length; while (n > 0 && s.charAt(n - 1) === ch) n--; return s.slice(0, n); }
function trimEndNonChar(s, ch) { let n = s.length; while (n > 0 && s.charAt(n - 1) !== ch) n--; return s.slice(0, n); }
// ge(): keep at most one trailing newline; drop two or more entirely.
function geStr(s) {
  const parts = s.split("\n");
  let t = parts.length - 1;
  while (t >= 0 && /^[ \t]*$/.test(parts[t])) t--;
  return parts.length - t <= 2 ? s : parts.slice(0, t + 1).join("\n");
}
// J(): expand tabs to spaces starting at column `col`.
function expandTabs(s, col) {
  let out = "", c = col;
  for (const ch of s) {
    if (ch === "\t") { const r = 4 - (c % 4); out += " ".repeat(r); c += r; }
    else { out += ch; c++; }
  }
  return out;
}
// Expand the leading whitespace of s to spaces.
function expandLeadWs(s) {
  let i = 0;
  while (i < s.length && (s.charCodeAt(i) === CC_SPACE || s.charCodeAt(i) === CC_TAB)) i++;
  if (i === 0) return s;
  return expandTabs(s.slice(0, i), 0) + s.slice(i);
}
// Strip n columns from the start of s (tabs count by column; a partially
// consumed tab becomes spaces).
function stripCols(s, n) {
  let col = 0, i = 0;
  while (i < s.length && col < n) {
    const c = s.charCodeAt(i);
    if (c === CC_SPACE) { col++; i++; }
    else if (c === CC_TAB) { const w = 4 - (col % 4); if (col + w > n) return " ".repeat(col + w - n) + s.slice(i + 1); col += w; i++; }
    else break;
  }
  return s.slice(i);
}
function trimEnd(s) { let n = s.length; while (n > 0 && (s.charCodeAt(n - 1) === CC_SPACE || s.charCodeAt(n - 1) === CC_TAB)) n--; return s.slice(0, n); }

// ---- line model -----------------------------------------------------------
// A line is { s: the line text (no \n), c: char offset where content starts }.
function mkLine(s) { return { s, c: 0 }; }
function lineText(L) { return L.s.slice(L.c); }
function isBlank(L) {
  for (let i = L.c; i < L.s.length; i++) {
    const c = L.s.charCodeAt(i);
    if (c !== CC_SPACE && c !== CC_TAB) return false;
  }
  return true;
}
// Leading whitespace: { cols: column count, idx: char index of first
// non-space char in L.s }.
function indentInfo(L) {
  let col = 0, i = L.c;
  while (i < L.s.length) {
    const c = L.s.charCodeAt(i);
    if (c === CC_SPACE) { col++; i++; }
    else if (c === CC_TAB) { col += 4 - (col % 4); i++; }
    else break;
  }
  return { cols: col, idx: i };
}
// Skip n columns of indentation; returns a new line.
function skipIndent(L, n) {
  let col = 0, i = L.c;
  while (i < L.s.length && col < n) {
    const c = L.s.charCodeAt(i);
    if (c === CC_SPACE) { col++; i++; }
    else if (c === CC_TAB) {
      const w = 4 - (col % 4);
      if (col + w > n) return { s: " ".repeat(col + w - n) + L.s.slice(i + 1), c: 0 };
      col += w; i++;
    } else break;
  }
  return { s: L.s, c: i };
}
// Index of the first non-space char in the line (char index in L.s).
function firstNonSpace(L) { return indentInfo(L).idx; }

// ---- block recognisers ----------------------------------------------------
// ATX heading: { depth, text } or null.
function atxInfo(L) {
  const info = indentInfo(L);
  if (info.cols > 3) return null;
  const s = L.s;
  let i = info.idx, depth = 0;
  while (i < s.length && s.charCodeAt(i) === CC_HASH) { i++; depth++; }
  if (depth === 0 || depth > 6) return null;
  if (i < s.length && s.charCodeAt(i) !== CC_SPACE && s.charCodeAt(i) !== CC_TAB) return null;
  let text = s.slice(i).trim();
  if (/#$/.test(text)) {
    const stripped = trimEndChar(text, "#");
    if (stripped === "" || /[ \t]$/.test(stripped)) text = stripped.trim();
  }
  return { depth, text };
}
// Fenced code: { ch, len, info, indent } or null.
function fenceInfo(L) {
  const info = indentInfo(L);
  if (info.cols > 3) return null;
  const s = L.s;
  let i = info.idx;
  const ch = s.charCodeAt(i);
  if (ch !== CC_BACKTICK && ch !== CC_TILDE) return null;
  let len = 0;
  while (i < s.length && s.charCodeAt(i) === ch) { i++; len++; }
  if (len < 3) return null;
  const rest = s.slice(i);
  if (ch === CC_BACKTICK && rest.includes("`")) return null;
  return { ch, len, info: rest.trim(), indent: info.cols };
}
// Thematic break: the marker char (*, -, _) or null.
function hrInfo(L) {
  const info = indentInfo(L);
  if (info.cols > 3) return null;
  const s = L.s.slice(info.idx);
  const m = /^([*_-])(?:[ \t]*\1){2,}[ \t]*$/.exec(s);
  return m ? m[1] : null;
}
// Blockquote marker: char index in L.s where the content starts, or -1.
function blockquoteMarker(L) {
  const info = indentInfo(L);
  if (info.cols > 3) return -1;
  if (L.s.charCodeAt(info.idx) !== CC_GT) return -1;
  let i = info.idx + 1;
  if (i < L.s.length && (L.s.charCodeAt(i) === CC_SPACE || L.s.charCodeAt(i) === CC_TAB)) i++;
  return i;
}
// List marker: { ordered, start, markerLen, bullet } or null.
function listMarker(L) {
  const info = indentInfo(L);
  if (info.cols > 3) return null;
  const s = L.s;
  let i = info.idx;
  const c = s.charCodeAt(i);
  if (c === CC_DASH || c === 43 || c === CC_ASTERISK) {
    const nx = s.charCodeAt(i + 1);
    if (i + 1 >= s.length || nx === CC_SPACE || nx === CC_TAB) {
      return { ordered: false, start: 0, markerLen: 1, bullet: s[i] };
    }
    return null;
  }
  if (c >= 48 && c <= 57) {
    let j = i, digits = 0;
    while (j < s.length && s.charCodeAt(j) >= 48 && s.charCodeAt(j) <= 57 && digits < 10) { j++; digits++; }
    if (digits === 0 || digits > 9) return null;
    const d = s.charCodeAt(j);
    if (d !== 46 && d !== 41) return null;
    const nx = s.charCodeAt(j + 1);
    if (j + 1 < s.length && nx !== CC_SPACE && nx !== CC_TAB) return null;
    return { ordered: true, start: parseInt(s.slice(i, j), 10), markerLen: j - i + 1, bullet: s.slice(i, j + 1) };
  }
  return null;
}
// Setext underline: 1 for =, 2 for -, else 0.
function setextInfo(L) {
  const info = indentInfo(L);
  if (info.cols > 3) return 0;
  const s = L.s.slice(info.idx);
  if (/^=+[ \t]*$/.test(s)) return 1;
  if (/^-+[ \t]*$/.test(s)) return 2;
  return 0;
}
// Block tags (marked's K list) for HTML block type 6.
const BLOCK_TAGS = new Set("address article aside base basefont blockquote body caption center col colgroup dd details dialog dir div dl dt fieldset figcaption figure footer form frame frameset h1 h2 h3 h4 h5 h6 head header hr html iframe legend li link main menu menuitem meta nav noframes ol optgroup option p param search section summary table tbody td tfoot th thead title tr track ul".split(" "));
// Is s (a line, leading spaces already stripped) exactly one complete
// open or close tag (type 7)? `after` is the text after the tag name.
function isCompleteTag(s) {
  // close tag: </name  > then only spaces/tabs
  const cm = /^<\/([a-zA-Z][a-zA-Z0-9-]*)[ \t]*>$/.exec(s);
  if (cm) return true;
  // open tag: <name (attributes)*  /?> then only spaces/tabs; a > (or />)
  // must actually be present -- a line that ends inside an attribute value
  // is not a complete tag
  if (s.charCodeAt(0) !== CC_LT || s.charCodeAt(1) === CC_SLASH) return false;
  let i = 1;
  while (i < s.length && ((s.charCodeAt(i) >= 65 && s.charCodeAt(i) <= 90) || (s.charCodeAt(i) >= 97 && s.charCodeAt(i) <= 122) || (s.charCodeAt(i) >= 48 && s.charCodeAt(i) <= 57) || s.charCodeAt(i) === CC_DASH)) i++;
  if (i === 1) return false;
  let closed = false;
  while (i < s.length) {
    // skip whitespace; an attribute must be preceded by whitespace
    let hadWs = false;
    while (i < s.length && (s.charCodeAt(i) === CC_SPACE || s.charCodeAt(i) === CC_TAB || s.charCodeAt(i) === CC_NL)) { i++; hadWs = true; }
    if (i >= s.length) break;
    const c = s.charCodeAt(i);
    if (c === CC_GT) { i++; closed = true; break; }
    if (c === CC_SLASH && s.charCodeAt(i + 1) === CC_GT) { i += 2; closed = true; break; }
    if (!hadWs) return false;
    // attribute name
    if (!((c >= 65 && c <= 90) || (c >= 97 && c <= 122) || c === 95 || c === CC_COLON)) return false;
    while (i < s.length) {
      const ch = s.charCodeAt(i);
      if ((ch >= 65 && ch <= 90) || (ch >= 97 && ch <= 122) || (ch >= 48 && ch <= 57) || ch === 95 || ch === CC_COLON || ch === 46 || ch === CC_DASH) i++;
      else break;
    }
    // optional = value; if there is no =, leave i right after the name so
    // the whitespace stays for the next attribute's hadWs check
    let d = i;
    while (d < s.length && (s.charCodeAt(d) === CC_SPACE || s.charCodeAt(d) === CC_TAB)) d++;
    if (s.charCodeAt(d) === CC_EQ) {
      i = d + 1;
      while (i < s.length && (s.charCodeAt(i) === CC_SPACE || s.charCodeAt(i) === CC_TAB)) i++;
      const q = s.charCodeAt(i);
      if (q === CC_DQUOTE || q === 39) {
        i++;
        while (i < s.length && s.charCodeAt(i) !== q && s.charCodeAt(i) !== CC_NL) i++;
        if (i >= s.length) return false;
        i++;
      } else {
        let ok = false;
        while (i < s.length) {
          const ch = s.charCodeAt(i);
          if (ch === CC_SPACE || ch === CC_TAB || ch === CC_DQUOTE || ch === 39 || ch === CC_EQ || ch === CC_LT || ch === CC_GT || ch === CC_BACKTICK) break;
          i++; ok = true;
        }
        if (!ok) return false;
      }
    }
  }
  while (i < s.length && (s.charCodeAt(i) === CC_SPACE || s.charCodeAt(i) === CC_TAB)) i++;
  return closed && i === s.length;
}
// HTML block type (1-7) for the line, or 0. Follows marked's Ue rules.
function htmlBlockType(L) {
  const info = indentInfo(L);
  if (info.cols > 3) return 0;
  const s = L.s.slice(info.idx);
  if (s.charCodeAt(0) !== CC_LT) return 0;
  if (/^<(script|pre|style|textarea)(?:[\s>]|$)/i.test(s)) return 1;
  if (s.startsWith("<!--")) return 2;
  if (s.startsWith("<?")) return 3;
  if (s.startsWith("<!") && s.length > 2 && s.charCodeAt(2) >= 65 && s.charCodeAt(2) <= 90) return 4;
  if (s.startsWith("<![CDATA[")) return 5;
  const m6 = /^<\/?([a-zA-Z][a-zA-Z0-9-]*)/.exec(s);
  if (m6) {
    const tag = m6[1].toLowerCase();
    if (BLOCK_TAGS.has(tag)) {
      const after = s.slice(m6[0].length);
      if (after === "" || after.charCodeAt(0) === CC_SPACE || after.charCodeAt(0) === CC_TAB || after.charCodeAt(0) === CC_GT || after.startsWith("/>")) return 6;
    }
  }
  // type 7: a complete open/close tag of a non-block tag, EOL after it
  if (isCompleteTag(s.trimEnd())) return 7;
  return 0;
}
// HTML block type for the paragraph-interruption check (type 6 allows only
// space, > , /> or EOL after the tag name -- no tab).
function htmlBeginType(L) {
  const info = indentInfo(L);
  if (info.cols > 3) return 0;
  const s = L.s.slice(info.idx);
  if (s.charCodeAt(0) !== CC_LT) return 0;
  if (/^<(script|pre|style|textarea)(?:[\s>]|$)/i.test(s)) return 1;
  if (s.startsWith("<!--")) return 2;
  if (s.startsWith("<?")) return 3;
  if (s.startsWith("<!") && s.length > 2 && s.charCodeAt(2) >= 65 && s.charCodeAt(2) <= 90) return 4;
  if (s.startsWith("<![CDATA[")) return 5;
  const m6 = /^<\/?([a-zA-Z][a-zA-Z0-9-]*)/.exec(s);
  if (m6) {
    const tag = m6[1].toLowerCase();
    if (BLOCK_TAGS.has(tag)) {
      const after = s.slice(m6[0].length);
      if (after === "" || after.charCodeAt(0) === CC_SPACE || after.charCodeAt(0) === CC_GT || after.startsWith("/>")) return 6;
    }
  }
  return 0;
}
// Table delimiter row: the align array or null. Each cell must be
// :?-+:? (spaces allowed); the row must contain a : or a |.
function tableDelimiter(L) {
  const s = lineText(L);
  if (!s.includes(":") && !s.includes("|")) return null;
  let cells = s.split("|");
  if (cells.length > 0 && cells[0].trim() === "") cells.shift();
  if (cells.length > 0 && cells[cells.length - 1].trim() === "") cells.pop();
  if (cells.length === 0) return null;
  const aligns = [];
  for (const cell of cells) {
    if (!/^ *:?-+:? *$/.test(cell)) return null;
    if (/^ *-+: *$/.test(cell)) aligns.push("right");
    else if (/^ *:-+: *$/.test(cell)) aligns.push("center");
    else if (/^ *:-+ *$/.test(cell)) aligns.push("left");
    else aligns.push(null);
  }
  return aligns;
}
// Can this line interrupt a paragraph? (ATX, fence, hr, html 1-6,
// blockquote, or a list that can interrupt.)
function interruptsPara(L) {
  if (atxInfo(L)) return true;
  if (fenceInfo(L)) return true;
  if (hrInfo(L)) return true;
  if (htmlBeginType(L) >= 1 && htmlBeginType(L) <= 6) return true;
  if (blockquoteMarker(L) >= 0) return true;
  if (listInterruptsPara(L)) return true;
  return false;
}
// A list marker that can interrupt a paragraph: bullet any, or ordered
// starting with 1, followed by [ \t]+ and a non-space char.
function listInterruptsPara(L) {
  const m = listMarker(L);
  if (!m) return false;
  if (m.ordered && m.start !== 1) return false;
  const s = L.s;
  let i = firstNonSpace(L) + m.markerLen;
  let sp = 0;
  while (i < s.length && (s.charCodeAt(i) === CC_SPACE || s.charCodeAt(i) === CC_TAB)) { i++; sp++; }
  if (sp === 0) return false;
  return i < s.length;
}
// A list marker followed by exactly one space/tab (for table rows).
function listEndsTableRow(L) {
  const m = listMarker(L);
  if (!m) return false;
  const s = L.s;
  const i = firstNonSpace(L) + m.markerLen;
  return i < s.length && (s.charCodeAt(i) === CC_SPACE || s.charCodeAt(i) === CC_TAB);
}
// Does this line start a block (for table body rows)? ATX, fence, hr,
// html, blockquote, list, indented code.
function startsBlock(L) {
  if (atxInfo(L) || fenceInfo(L) || hrInfo(L)) return true;
  if (htmlBlockType(L) > 0) return true;
  if (blockquoteMarker(L) >= 0) return true;
  if (listMarker(L)) return true;
  const info = indentInfo(L);
  // Indented code is (?: {4}| {0,3}\t) followed by ANY non-newline char
  // (a trailing space counts, so " \t " is code but a lone "\t" is not).
  if (info.cols >= 4 && lineText(skipIndent(L, 4)).length > 0) return true;
  return false;
}
// Is this line exactly one tag (for lheading)? e.g. <div>
function lheadingHtmlLine(L) {
  const s = lineText(L).trim();
  return /^<[^>]*>$/.test(s) && !s.includes("\n");
}

// ---- paren matching (ke) and title scanning -------------------------------
// ke(s, "()"): -1 when no parens or balanced, -2 when an unclosed (,
// else the index of an unmatched ).
function keParen(s) {
  if (s.indexOf("(") === -1 && s.indexOf(")") === -1) return -1;
  let t = 0;
  for (let n = 0; n < s.length; n++) {
    if (s[n] === "\\") n++;
    else if (s[n] === "(") t++;
    else if (s[n] === ")") { t--; if (t < 0) return n; }
  }
  return t > 0 ? -2 : -1;
}
// Scan a link title at position r of e. Returns {text, end} or null.
function scanTitle(e, r) {
  const q = e.charCodeAt(r);
  if (q === CC_DQUOTE) {
    let i = r + 1;
    while (i < e.length) {
      const c = e.charCodeAt(i);
      if (c === CC_BACKSLASH && i + 1 < e.length) { i += 2; continue; }
      if (c === CC_DQUOTE) return { text: e.slice(r + 1, i), end: i + 1 };
      i++;
    }
    return null;
  }
  if (q === 39) {
    let i = r + 1;
    while (i < e.length) {
      const c = e.charCodeAt(i);
      if (c === CC_BACKSLASH && i + 1 < e.length) { i += 2; continue; }
      if (c === CC_NL) {
        if (i + 1 < e.length && e.charCodeAt(i + 1) === CC_NL) return null;
        i++; continue;
      }
      if (c === 39) return { text: e.slice(r + 1, i), end: i + 1 };
      i++;
    }
    return null;
  }
  if (q === CC_LPAREN) {
    let i = r + 1;
    while (i < e.length) {
      const c = e.charCodeAt(i);
      if (c === CC_BACKSLASH && i + 1 < e.length) { i += 2; continue; }
      if (c === CC_LPAREN || c === CC_RPAREN) {
        if (c === CC_RPAREN) return { text: e.slice(r + 1, i), end: i + 1 };
        return null;
      }
      if (c === CC_NL) return null;
      i++;
    }
    return null;
  }
  return null;
}
// ---- fence content compensation (Dt) --------------------------------------
// Strip up to n leading whitespace *characters* from s (backtick fences only).
function stripWsChars(s, n) {
  let i = 0;
  while (i < s.length && i < n && (s.charCodeAt(i) === CC_SPACE || s.charCodeAt(i) === CC_TAB)) i++;
  return s.slice(i);
}
// ---- table helpers --------------------------------------------------------
// Is this line a delimiter-shaped row (cells :?-+:?), without the :/| test?
function isDelimiterRow(L) {
  const s = lineText(L);
  if (!s.includes(":") && !s.includes("|")) return false;
  let cells = s.split("|");
  if (cells.length > 0 && cells[0].trim() === "") cells.shift();
  if (cells.length > 0 && cells[cells.length - 1].trim() === "") cells.pop();
  if (cells.length === 0) return false;
  for (const cell of cells) if (!/^ *:?-+:? *$/.test(cell)) return false;
  return true;
}
// Is lines[i] a table header (the next line is a delimiter row)?
function tableHeaderAt(lines, i, end) {
  if (i + 1 >= end) return false;
  if (isBlank(lines[i])) return false;
  return isDelimiterRow(lines[i + 1]);
}
// de(): split a table row into cells (naive | split, code spans ignored).
function deCells(s, count) {
  let t = "";
  for (let i = 0; i < s.length; i++) {
    if (s[i] === "|") {
      let l = false, p = i;
      while (--p >= 0 && s[p] === "\\") l = !l;
      t += l ? "|" : " |";
    } else t += s[i];
  }
  let n = t.split(" |");
  if (n.length > 0 && n[0].trim() === "") n.shift();
  if (n.length > 0 && n[n.length - 1].trim() === "") n.pop();
  if (count !== undefined) {
    if (n.length > count) n.length = count;
    else while (n.length < count) n.push("");
  }
  for (let i = 0; i < n.length; i++) n[i] = n[i].trim().replace(/\\\|/g, "|");
  return n;
}
// ---- block functions ------------------------------------------------------
// Indented code. Returns {text, next} or null.
function tryCode(lines, i, end) {
  const info = indentInfo(lines[i]);
  if (info.cols < 4) return null;
  let j = i;
  while (j < end) {
    if (isBlank(lines[j])) { j++; continue; }
    if (indentInfo(lines[j]).cols < 4) break;
    j++;
  }
  // back up over trailing blank lines (they are skipped by the caller)
  let last = j - 1;
  while (last >= i && isBlank(lines[last])) last--;
  if (last < i) return null;
  let text = "";
  for (let k = i; k <= last; k++) {
    const line = skipIndent(lines[k], 4);
    text += (k > i ? "\n" : "") + lineText(line);
  }
  text = geStr(text);
  return { text, next: last + 1 };
}
// Fenced code. Returns {text, lang, next} or null.
function tryFence(lines, i, end) {
  const f = fenceInfo(lines[i]);
  if (!f) return null;
  let j = i + 1, closed = false;
  while (j < end) {
    const Lj = lines[j];
    const info = indentInfo(Lj);
    if (info.cols <= 3) {
      const s = Lj.s;
      let k = info.idx;
      if (s.charCodeAt(k) === f.ch) {
        let len = 0;
        while (k < s.length && s.charCodeAt(k) === f.ch) { k++; len++; }
        if (len >= f.len) {
          let ok = true;
          while (k < s.length) { if (s.charCodeAt(k) !== CC_SPACE) { ok = false; break; } k++; }
          if (ok) { closed = true; break; }
        }
      }
    }
    j++;
  }
  const contentEnd = closed ? j : end;
  let text = "";
  for (let k = i + 1; k < contentEnd; k++) {
    let line = lines[k].s;
    if (f.ch === CC_BACKTICK) line = stripWsChars(line, f.indent);
    text += (k > i + 1 ? "\n" : "") + line;
  }
  // marked unescapes backslash escapes in the info string (the lang field)
  return { text, lang: unescapePunct(f.info), next: closed ? j + 1 : end };
}
// ATX heading. Returns {depth, text} or null.
function tryHeading(lines, i) {
  const h = atxInfo(lines[i]);
  if (!h) return null;
  return { depth: h.depth, text: h.text };
}
// Collect the paragraph lines starting at i (for lheading or paragraph).
// forLheading: also stop at a line that is exactly one HTML tag, and at a
// setext underline (the lheading rule is non-greedy).
// A whitespace-only line is NOT a blank line when it is the last line and
// the source does not end with \n (marked's paragraph regex requires a
// \n after the spaces for it to count as blank, so a trailing " " line
// continues the paragraph: "> \n> foo\n>  " -> paragraph "foo\n ").
function collectParaLines(lines, i, end, forLheading) {
  let j = i + 1;
  while (j < end) {
    const Lj = lines[j];
    // A whitespace-only line ends the paragraph, except a non-empty one
    // (e.g. a single " ") that is the last line with no trailing \n --
    // marked's paragraph regex needs a \n after the spaces to count it
    // as blank, so it continues the paragraph instead. An empty line
    // (zero chars) always ends it.
    if (isBlank(Lj) && !(Lj.s.length > 0 && j === end - 1 && !lines.endsNL)) break;
    if (interruptsPara(Lj)) break;
    if (forLheading && lheadingHtmlLine(Lj)) break;
    if (forLheading && setextInfo(Lj) > 0) break;
    if (tableHeaderAt(lines, j, end)) break;
    j++;
  }
  return j;
}
// Setext heading. Returns {depth, text, next} or null.
function tryLheading(lines, i, end) {
  const j = collectParaLines(lines, i, end, true);
  if (j >= end) return null;
  const depth = setextInfo(lines[j]);
  if (depth === 0) return null;
  let text = "";
  for (let k = i; k < j; k++) text += (k > i ? "\n" : "") + lineText(lines[k]);
  text = text.trim();
  return { depth, text, next: j + 1 };
}
// Table. Returns {head, aligns, rows, next} or null.
function tryTable(lines, i, end, refs) {
  if (i + 1 >= end) return null;
  const aligns = tableDelimiter(lines[i + 1]);
  if (!aligns) return null;
  const head = deCells(lineText(lines[i]).trim());
  if (head.length !== aligns.length) return null;
  const rows = [];
  let j = i + 2;
  while (j < end) {
    const Lj = lines[j];
    // A table body row ends at a spaces-only line (marked's row lookahead
    // excludes only " *\n"); a lone-tab line is a ROW (an empty row), not
    // a blank line, and a " \t " line is indented code (startsBlock).
    if (/^ *$/.test(lineText(Lj))) break;
    if (startsBlock(Lj)) break;
    rows.push(deCells(lineText(Lj).trim(), head.length));
    j++;
  }
  return { head, aligns, rows, next: j };
}
// Link reference definition. Returns {tag, href, title, next} or null.
const RE_DEF = /^ {0,3}\[((?!\s*\])(?:\\[\s\S]|[^\[\]\\\n]|\n(?![ \t]*\n))+)\]: *(?:\n[ \t]*)?([^<\s][^\s]*|<.*?>)(?:(?: +(?:\n[ \t]*)?| *\n[ \t]*)(("(?:\\[\s\S]|[^"\\])*")|'(?:\\[\s\S]|[^'\\\n]|\n(?!\n))*'|\((?:\\[\s\S]|[^()\\])*\)))? *(?:\n+|$)/;
function tryDef(lines, i, end) {
  // A def's title can span several lines; include lines up to the next
  // blank line (a def cannot contain one) capped at 10 lines.
  let k = i;
  while (k < end && !isBlank(lines[k]) && k < i + 10) k++;
  let cand = "";
  for (let q = i; q < k; q++) cand += (q > i ? "\n" : "") + lines[q].s;
  cand += "\n";
  const m = RE_DEF.exec(cand);
  if (!m) return null;
  const dest = m[2];
  const angle = dest.charCodeAt(0) === CC_LT;
  if (!angle && keParen(dest) !== -1) return null;
  let href = angle ? dest.slice(1, -1) : dest;
  href = unescapePunct(href);
  let title = null;
  if (m[3] !== undefined) title = unescapePunct(m[3].slice(1, -1));
  const tag = normLabel(m[1]);
  // lines consumed: newlines in the match before the trailing \n+
  const body = m[0].replace(/\n+$/, "");
  let nl = 0;
  for (let q = 0; q < body.length; q++) if (body.charCodeAt(q) === CC_NL) nl++;
  return { tag, href, title, next: i + 1 + nl };
}
// HTML block. Returns {text, next} or null.
// Types 1-5 end at the closing marker; the text gets one trailing \n when
// the closing line is followed by a non-blank line, or at EOF when the
// source ends with \n (lines.endsNL). Types 6/7 end at a blank line with
// no trailing \n.
function htmlCloseTagEOL(s, tag) {
  // A literal </tag> (case-insensitive) anywhere in the line.
  return s.toLowerCase().includes("</" + tag + ">");
}
function tryHtml(lines, i, end) {
  const type = htmlBlockType(lines[i]);
  if (type === 0) return null;
  if (type === 6 || type === 7) {
    // ends at a blank line; the text has a trailing \n only at EOF when
    // the source ends with \n (ge drops the blank line's newlines)
    let j = i;
    while (j < end && !isBlank(lines[j])) j++;
    let text = "";
    for (let k = i; k < j; k++) text += (k > i ? "\n" : "") + lines[k].s;
    if (j >= end && !!lines.endsNL) text += "\n";
    return { text, next: j };
  }
  // types 1-5: end at the closing marker
  let j = i, closed = false;
  const firstLine = lines[i].s;
  const has = (sub) => lines[j].s.includes(sub);
  if (type === 1) {
    const m = /^ {0,3}<(script|pre|style|textarea)(?:[\s>]|$)/i.exec(firstLine);
    const tag = m ? m[1].toLowerCase() : "";
    for (; j < end; j++) if (htmlCloseTagEOL(lines[j].s, tag)) { closed = true; j++; break; }
    if (!closed) j = end;
  } else if (type === 2) {
    for (; j < end; j++) if (has("-->")) { closed = true; j++; break; }
    if (!closed) j = end;
  } else if (type === 3) {
    for (; j < end; j++) if (has("?>")) { closed = true; j++; break; }
    if (!closed) j = end;
  } else if (type === 4) {
    for (; j < end; j++) if (has(">")) { closed = true; j++; break; }
    if (!closed) j = end;
  } else if (type === 5) {
    for (; j < end; j++) if (has("]]>")) { closed = true; j++; break; }
    if (!closed) j = end;
  }
  let text = "";
  for (let k = i; k < j; k++) text += (k > i ? "\n" : "") + lines[k].s;
  // Trailing \n when the next line is non-empty (any whitespace-only line
  // counts -- only a truly empty line drops it) or at EOF with endsNL.
  if (j < end ? lineText(lines[j]).length > 0 : !!lines.endsNL) text += "\n";
  text = geStr(text);
  return { text, next: j };
}
// Paragraph. Returns {text, next}.
function collectParagraph(lines, i, end) {
  const j = collectParaLines(lines, i, end, false);
  let text = "";
  for (let k = i; k < j; k++) text += (k > i ? "\n" : "") + lineText(lines[k]);
  return { text, next: j };
}

// ---- list machinery -------------------------------------------------------
// R-limited break checks (applied to the raw line, counting spaces).
// marked's D() clamps the limit to R-1, in [0,3]. The regexes are
// precompiled once (indexed by the clamped limit 0..3) -- constructing
// them per call was the top CPU hotspot.
function rLimit(R) { return Math.max(0, Math.min(3, R - 1)); }
const _FENCE_R = [0, 1, 2, 3].map((n) => new RegExp(`^ {0,${n}}(?:\`\`\`|~~~)`));
const _HEADING_R = [0, 1, 2, 3].map((n) => new RegExp(`^ {0,${n}}#{1,6}(?:\\s|$)`));
const _HTML_R = [0, 1, 2, 3].map((n) => new RegExp(`^ {0,${n}}(?:</?(?:${[...BLOCK_TAGS].join("|")})(?: +|$|/?>)|<(?:(?:script|pre|style|textarea)(?:[\\s>]|$)|!--)|<\\?|<![A-Za-z]|<!\\[CDATA\\[)`, "i"));
const _BQ_R = [0, 1, 2, 3].map((n) => new RegExp(`^ {0,${n}}>`));
const _BULLET_R = [0, 1, 2, 3].map((n) => new RegExp(`^ {0,${n}}(?:[*+-]|\\d{1,9}[.)])((?:[ \\t][^\\n]*)?(?:\\n|$))`));
const _HR_R = [0, 1, 2, 3].map((n) => new RegExp(`^ {0,${n}}((?:-[ \\t]*){3,}|(?:_[ \\t]*){3,}|(?:\\*[ \\t]*){3,})(?:\\n+|$)`));
function fenceBeginR(s, R) { return _FENCE_R[rLimit(R)].test(s); }
function headingBeginR(s, R) { return _HEADING_R[rLimit(R)].test(s); }
function htmlBeginR(s, R) { return _HTML_R[rLimit(R)].test(s); }
function blockquoteBeginR(s, R) { return _BQ_R[rLimit(R)].test(s); }
function nextBulletR(s, R) { return _BULLET_R[rLimit(R)].test(s); }
function hrR(s, R) { return _HR_R[rLimit(R)].test(s); }
// Fast pre-check: could this raw line start a block (fence/heading/html/
// blockquote/list/hr) within the R-limited leading spaces? The R-limited
// regexes all anchor on a block-start char after 0..rLimit spaces, so a
// line whose first non-space char (within the limit) is not one of those
// chars cannot match any of them -- skip all six regex tests.
function couldStartBlockR(s, R) {
  const lim = rLimit(R);
  let i = 0;
  while (i < s.length && s.charCodeAt(i) === CC_SPACE && i < lim) i++;
  if (i >= s.length) return false;
  const c = s.charCodeAt(i);
  if (i > lim) return false;
  return c === CC_BACKTICK || c === 126 || c === 35 || c === CC_LT || c === 62 ||
    c === 45 || c === 43 || c === 42 || c === 95 || (c >= 48 && c <= 57);
}
// Parse one list item starting at lines[j] (a marker line). Returns
// {text, next, rawLines, R} or null.
function parseListItem(lines, j, end, marker) {
  const L = lines[j];
  const info = indentInfo(L);
  const markerEndIdx = info.idx + marker.markerLen;
  const rest = L.s.slice(markerEndIdx);
  const b = info.cols + marker.markerLen;
  let col = b, k = 0, wsCols = 0;
  while (k < rest.length && (rest.charCodeAt(k) === CC_SPACE || rest.charCodeAt(k) === CC_TAB)) {
    if (rest.charCodeAt(k) === CC_SPACE) { col++; wsCols++; k++; }
    else { const w = 4 - (col % 4); col += w; wsCols += w; k++; }
  }
  const isEmpty = rest.trim() === "";
  let R, firstContent;
  if (isEmpty) {
    R = b + 1;
    firstContent = "";
  } else {
    const strip = wsCols > 4 ? 1 : wsCols;
    R = b + strip;
    const expandedRest = expandTabs(rest.slice(0, k), b) + rest.slice(k);
    firstContent = expandedRest.slice(strip);
  }
  // empty item followed by a blank line: the item is just the marker
  if (isEmpty && j + 1 < end && isBlank(lines[j + 1])) {
    return { text: "", next: j + 2, rawLines: lines.slice(j, j + 2), R, isEmpty: true };
  }
  const textLines = [firstContent];
  let next = j + 1;
  let m = firstContent;
  let prevBlank = isEmpty;
  while (next < end) {
    const rawLine = lines[next].s;
    if (couldStartBlockR(rawLine, R) && (fenceBeginR(rawLine, R) || headingBeginR(rawLine, R) || htmlBeginR(rawLine, R) || blockquoteBeginR(rawLine, R) || nextBulletR(rawLine, R) || hrR(rawLine, R))) break;
    const Z = expandLeadWs(rawLine);
    const firstNS = Z.search(/[^ ]/);
    if (firstNS >= R || rawLine.trim() === "") {
      textLines.push(Z.slice(R));
      prevBlank = rawLine.trim() === "";
      m = Z.slice(R);
      next++;
    } else {
      const mExp = m.replace(/\t/g, "    ");
      const mNS = mExp.search(/[^ ]/);
      if (prevBlank || mNS >= 4 || (couldStartBlockR(m, R) && (fenceBeginR(m, R) || headingBeginR(m, R) || htmlBeginR(m, R) || hrR(m, R)))) break;
      let qe = rawLine;
      if (/^ {0,3}(?:=+|-+) *$/.test(rawLine) && m.trim() !== "") {
        qe = "    " + Z.replace(/^ {0,3}/, "");
      }
      textLines.push(qe);
      prevBlank = false;
      m = Z.slice(R);
      next++;
    }
  }
  return { text: textLines.join("\n"), next, rawLines: lines.slice(j, next), R, isEmpty: false };
}
// Is this item text a task item? Returns {checked} or null.
function taskInfo(text) {
  const m = /^\[[ xX]\][ \t]+\S/.exec(text);
  if (!m) return null;
  return { checked: text.charCodeAt(1) !== CC_SPACE };
}
function hasDoubleBlank(s) { return /\n[ \t]*\n[ \t]*$/.test(s); }
// List. Returns {ordered, start, loose, items, next} or null.
function tryList(lines, i, end, refs) {
  const first = listMarker(lines[i]);
  if (!first) return null;
  if (hrInfo(lines[i])) return null;
  const ordered = first.ordered;
  const start = first.start;
  const delim = ordered ? first.bullet.slice(-1) : first.bullet;
  const items = [];
  let loose = false;
  let p = false;
  let j = i;
  while (j < end) {
    const L = lines[j];
    const mk = listMarker(L);
    if (!mk) break;
    if (ordered) {
      if (!mk.ordered || mk.bullet.slice(-1) !== delim) break;
    } else {
      if (mk.ordered || mk.bullet !== delim) break;
    }
    if (hrInfo(L)) break;
    const item = parseListItem(lines, j, end, mk);
    if (!item) break;
    items.push(item);
    // marked's item raw A = source slice up to the current position, so it
    // ends with \n when the item is followed by more lines (or the source
    // ends with \n); that trailing \n is what doubleBlankLine detects
    const rawStr = item.rawLines.map((x) => x.s).join("\n") + (item.next < end || lines.endsNL ? "\n" : "");
    if (!loose) {
      if (p) loose = true;
      else if (hasDoubleBlank(rawStr)) p = true;
    }
    j = item.next;
  }
  if (items.length === 0) return null;
  // trim the last item's text
  const lastItem = items[items.length - 1];
  lastItem.text = lastItem.text.replace(/[ \t]+$/, "");
  // endsNL for a sub-parse is true only when the item is the last one AND
  // the list consumed to the end of the source (a non-last item's html
  // block must not get a trailing \n)
  const listAtEOF = (j >= end) && !!lines.endsNL;
  // parse each item's blocks; handle tasks; detect loose via blankSep
  const parsed = [];
  for (const item of items) {
    const itemLines = item.text === "" ? [] : item.text.split("\n").map((s) => mkLine(s));
    itemLines.endsNL = (item === lastItem) && listAtEOF;
    const toks = [];
    const res = parseBlocks(itemLines, 0, itemLines.length, refs, false, toks, false);
    if (res.blankSep) loose = true;
    // task handling: parse unstripped first; if the first token is
    // text/paragraph and the text is a task, strip and re-parse
    let task = null;
    const ti = taskInfo(item.text);
    if (ti && toks.length > 0 && (toks[0].t === "x" || toks[0].t === "p")) {
      task = ti;
      const stripped = item.text.replace(/^\[[ xX]\][ \t]+/, "");
      const sl = stripped === "" ? [] : stripped.split("\n").map((s) => mkLine(s));
      sl.endsNL = (item === lastItem) && listAtEOF;
      const stoks = [];
      const sres = parseBlocks(sl, 0, sl.length, refs, false, stoks, false);
      if (sres.blankSep) loose = true;
      parsed.push({ task, checked: ti.checked, toks: stoks });
    } else {
      parsed.push({ task: null, checked: false, toks });
    }
  }
  if (loose) {
    for (const it of parsed) {
      for (const t of it.toks) if (t.t === "x") t.t = "p";
    }
  }
  const raw = lines.slice(i, j).map((x) => x.s).join("\n").replace(/[ \t\n]+$/, "");
  // marked trims the list token's raw, so the outer lexer advances only
  // past the last non-blank line and the trailing blank lines are lexed
  // as a space token (which is what makes an outer list loose when a
  // blank line follows a nested list). Back up over trailing blanks.
  let next = j;
  while (next > i && isBlank(lines[next - 1])) next--;
  return { ordered, start, loose, items: parsed, raw, next };
}
// ---- blockquote machinery -------------------------------------------------
// Is this line a lazy-break for a blockquote paragraph? (hr, ATX, fence,
// html 1-6, blockquote, any list marker)
function bqLazyBreak(L) {
  if (hrInfo(L) || atxInfo(L) || fenceInfo(L)) return true;
  const ht = htmlBeginType(L);
  if (ht >= 1 && ht <= 6) return true;
  if (blockquoteMarker(L) >= 0) return true;
  if (listMarker(L)) return true;
  return false;
}
// Does this blockquote-marker content start a paragraph (vs an indented
// code block, fence, heading, hr, or html block)? Only a paragraph allows
// lazy continuations, so ">     foo" (indented code) and "> ```" (fence)
// do not let the following unmarked line join the blockquote. A LIST item
// DOES allow them: the lazy line joins the innermost paragraph (e.g.
// "> 1. > Blockquote" + "continued here." -> the inner blockquote's
// paragraph is "Blockquote\ncontinued here.").
function contentStartsPara(content) {
  const L = mkLine(content);
  if (isBlank(L)) return false;
  if (indentInfo(L).cols >= 4) return false;
  if (fenceInfo(L) || atxInfo(L) || hrInfo(L)) return false;
  const ht = htmlBeginType(L);
  if (ht >= 1 && ht <= 6) return false;
  return true;
}
// Blockquote. Returns {toks, next} or null.
function tryBlockquote(lines, i, end, refs) {
  if (blockquoteMarker(lines[i]) < 0) return null;
  // collect the blockquote's lines (marker lines + lazy continuations)
  const bqLines = [];
  let j = i;
  let inPara = false;
  // A fence inside the blockquote suppresses lazy continuations until it
  // closes: a line after fence content is not a lazy paragraph line, even
  // though the content line itself looks like a paragraph start.
  let inFence = false, fenceCh = 0, fenceLen = 0;
  while (j < end) {
    const L = lines[j];
    const mi = blockquoteMarker(L);
    if (mi >= 0) {
      bqLines.push(L);
      const content = L.s.slice(mi);
      const CL = mkLine(content);
      if (inFence) {
        const f = fenceInfo(CL);
        if (f && f.ch === fenceCh && f.len >= fenceLen && f.info === "") inFence = false;
        inPara = false;
      } else {
        const f = fenceInfo(CL);
        if (f) { inFence = true; fenceCh = f.ch; fenceLen = f.len; inPara = false; }
        else inPara = contentStartsPara(content);
      }
      j++;
    } else if (inPara && !isBlank(L) && !bqLazyBreak(L)) {
      bqLines.push(L);
      j++;
    } else break;
  }
  if (bqLines.length === 0) return null;
  const bqEnd = j;
  const bqAtEOF = (bqEnd >= end) && !!lines.endsNL;
  const toks = [];
  let rawParts = [];
  let n = bqLines.slice();
  // chunk loop
  while (n.length > 0) {
    let seen = false;
    const chunk = [];
    let p = 0;
    for (; p < n.length; p++) {
      if (blockquoteMarker(n[p]) >= 0) { chunk.push(n[p]); seen = true; }
      else if (!seen) chunk.push(n[p]);
      else break;
    }
    n = n.slice(p);
    const h = chunk.map((x) => x.s).join("\n");
    // inner text: expand ws after >, setext-indent, strip markers
    let u = h.replace(/^( {0,3}>)([ \t]+)/gm, (g, b, m) => b + expandTabs(m, b.length));
    u = u.replace(/\n {0,3}((?:=+|-+)[ \t]*)(?=\n|$)/g, "\n    $1");
    u = u.replace(/^ {0,3}>[ \t]?/gm, "");
    rawParts.push(h);
    const chunkLines = u === "" ? [] : u.split("\n").map((s) => mkLine(s));
    // The chunk inner text u is built by joining lines, so it never ends
    // with \n: endsNL is false (an html block inside a blockquote never
    // gets a trailing \n, and a trailing " " line is a paragraph
    // continuation, not a blank line).
    chunkLines.endsNL = false;
    const before = toks.length;
    const mergeFirst = toks.length > 0 && toks[toks.length - 1].t === "p";
    // lex the chunk with top=true, merging its first paragraph into the
    // previous chunk's last paragraph
    const res = parseBlocks(chunkLines, 0, chunkLines.length, refs, true, toks, mergeFirst);
    void res;
    void before;
    if (n.length === 0) break;
    const k = toks[toks.length - 1];
    if (!k) break;
    if (k.t === "c" || k.t === "h" || k.t === "hr" || k.t === "html" || k.t === "table") break;
    if (k.t === "bq") {
      // nested blockquote: re-lex with remaining lines appended
      const g = k;
      const b = n.map((x) => x.s).join("\n");
      const mStr = (g.raw || "") + "\n" + b.replace(/^ {0,3}>[ \t]?/gm, "");
      const mLines = mStr === "" ? [] : mStr.split("\n").map((s) => mkLine(s));
      mLines.endsNL = false;
      const subToks = [];
      const subRes = parseBlocks(mLines, 0, mLines.length, refs, true, subToks, false);
      void subRes;
      // find the nested blockquote token in subToks
      const f = subToks.find((t) => t.t === "bq");
      if (!f) break;
      toks[toks.length - 1] = f;
      // how many of n's lines were consumed by the re-lexed blockquote?
      // (marked: the part of m past f.raw is the unconsumed remainder;
      // its line count R means the last R lines of n are unconsumed)
      const y = mStr.substring((f.raw || "").length).replace(/^\n/, "");
      const R = y === "" ? 0 : y.split("\n").length;
      const A = R ? n.slice(0, -R) : n;
      if (A.length > 0) rawParts.push(A.map((x) => x.s).join("\n"));
      n = n.slice(A.length);
      if (n.length > 0 && blockquoteMarker(n[0]) >= 0) continue;
      break;
    } else if (k.t === "list") {
      const g = k;
      const b = (g.raw || "") + "\n" + n.map((x) => x.s).join("\n");
      const bLines = b === "" ? [] : b.split("\n").map((s) => mkLine(s));
      bLines.endsNL = false;
      const subToks = [];
      const subRes = parseBlocks(bLines, 0, bLines.length, refs, true, subToks, false);
      void subRes;
      const mTok = subToks.find((t) => t.t === "list");
      if (!mTok) break;
      toks[toks.length - 1] = mTok;
      // Count the lines from n that the re-lexed list consumed, by
      // string-slicing like marked: the part of b past g.raw + "\n", up
      // to m.raw's length, split into lines.
      const gRaw = g.raw || "";
      const mRaw = mTok.raw || "";
      let fCount = 0;
      if (mRaw.length > gRaw.length) {
        const bStr = gRaw + "\n" + n.map((x) => x.s).join("\n");
        const added = bStr.slice(gRaw.length + 1, mRaw.length);
        fCount = added === "" ? 0 : added.split("\n").length;
      }
      if (fCount > 0) {
        const y = n.slice(0, fCount);
        rawParts.push(y.map((x) => x.s).join("\n"));
      }
      n = n.slice(fCount);
      continue;
    }
    // otherwise continue to the next chunk
  }
  const raw = rawParts.join("\n");
  return { toks, raw, next: j };
}

// ---- renderer -------------------------------------------------------------
function renderListItem(item, refs) {
  const cb = item.task ? '<input ' + (item.checked ? 'checked="" ' : '') + 'disabled="" type="checkbox"> ' : "";
  if (item.toks.length === 0) return cb;
  const first = item.toks[0];
  if (item.task && (first.t === "p" || first.t === "x")) {
    let out = "";
    if (first.t === "p") out += "<p>" + cb + inlineParse(first.text, refs, false) + "</p>\n";
    else out += cb + inlineParse(first.text, refs, false);
    out += renderTokens(item.toks.slice(1), refs);
    return out;
  }
  return cb + renderTokens(item.toks, refs);
}
function renderTokens(toks, refs) {
  let out = "";
  for (const tok of toks) {
    switch (tok.t) {
      case "c": {
        const lang = tok.lang ? tok.lang.match(/^\S*/)[0] : "";
        const text = tok.text ? tok.text.replace(/\n$/, "") + "\n" : "";
        out += lang ? '<pre><code class="language-' + lang + '">' + escFull(text) + "</code></pre>\n" : "<pre><code>" + escFull(text) + "</code></pre>\n";
        break;
      }
      case "h":
        out += "<h" + tok.depth + ">" + inlineParse(tok.text, refs, false) + "</h" + tok.depth + ">\n";
        break;
      case "hr":
        out += "<hr>\n";
        break;
      case "bq":
        out += "<blockquote>\n" + renderTokens(tok.toks, refs) + "</blockquote>\n";
        break;
      case "html":
        out += tok.text;
        break;
      case "p":
        out += "<p>" + inlineParse(tok.text, refs, false) + "</p>\n";
        break;
      case "x":
        out += inlineParse(tok.text, refs, false);
        break;
      case "list": {
        const tag = tok.ordered ? "ol" : "ul";
        const startAttr = tok.ordered && tok.start !== 1 ? ' start="' + tok.start + '"' : "";
        out += "<" + tag + startAttr + ">\n";
        for (const item of tok.items) out += "<li>" + renderListItem(item, refs) + "</li>\n";
        out += "</" + tag + ">\n";
        break;
      }
      case "table": {
        out += "<table>\n<thead>\n<tr>\n";
        for (let ci = 0; ci < tok.head.length; ci++) {
          const align = tok.aligns[ci];
          out += align ? '<th align="' + align + '">' : "<th>";
          out += inlineParse(tok.head[ci], refs, false);
          out += "</th>\n";
        }
        out += "</tr>\n</thead>\n";
        if (tok.rows.length > 0) {
          out += "<tbody>";
          for (const row of tok.rows) {
            out += "<tr>\n";
            for (let ci = 0; ci < row.length; ci++) {
              const align = tok.aligns[ci];
              out += align ? '<td align="' + align + '">' : "<td>";
              out += inlineParse(row[ci], refs, false);
              out += "</td>\n";
            }
            out += "</tr>\n";
          }
          out += "</tbody>";
        }
        out += "</table>\n";
        break;
      }
    }
  }
  return out;
}
// ---- top level ------------------------------------------------------------
let SRC_ENDS_NL = false;
export function parse(markdown) {
  const src = markdown.replace(/\r\n|\r/g, "\n");
  SRC_ENDS_NL = src.endsWith("\n");
  const parts = src.split("\n");
  if (parts.length > 0 && parts[parts.length - 1] === "") parts.pop();
  const lines = parts.map((s) => mkLine(s));
  lines.endsNL = SRC_ENDS_NL;
  const refs = {};
  const toks = [];
  resetInlineState();
  parseBlocks(lines, 0, lines.length, refs, true, toks, false);
  resetInlineState();
  return renderTokens(toks, refs);
}
