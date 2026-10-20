/* GRIDLOCK - city traffic monitor prototype. Pure C99 + raylib.
 * A 6x4 junction grid, cars that route with Floyd-Warshall, timed signals,
 * sensors/metrics, incidents and what-if controls.
 * Keys: P pause | 1/2/4 sim speed | C crash | S stadium | R rain | W roadworks | G green wave
 * Mouse: click a road to close/open it, ctrl+click for roadworks, scroll over a junction to retime it. */
#include "raylib.h"
#include "raymath.h"
#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define SW 1280
#define SH 800
#define GR 4
#define GC 6
#define NN (GR * GC)
#define NE 80
#define NCAR 420
#define NFEED 5
#define NDROP 90
#define PXK 0.3f      /* pixels per (km/h * second) */
#define CLOCKX 40.0f  /* city clock seconds per sim second */
#define V_LOC 50.0f   /* local road speed limit, km/h */
#define V_ART 80.0f   /* arterial road speed limit, km/h */

#define C_BG     (Color){10,12,22,255}
#define C_CARD   (Color){19,23,40,255}
#define C_BORDER (Color){35,41,66,255}
#define C_ROAD   (Color){30,35,60,255}
#define C_ART    (Color){50,58,96,255}
#define C_TEXT   (Color){236,239,252,255}
#define C_MUTED  (Color){128,138,170,255}
#define C_CYAN   (Color){56,224,255,255}
#define C_VIOLET (Color){139,92,246,255}
#define C_PINK   (Color){255,87,170,255}
#define C_GREEN  (Color){52,230,160,255}
#define C_AMBER  (Color){255,190,70,255}
#define C_RED    (Color){255,84,104,255}

enum { AL, AC, AR };
typedef struct { float x, y, cycle, off, q; } Node;
typedef struct { int a, b, horiz, art, closed, cnt; float len, limit, crash, ratio, ux, uy, works; } Edge;
typedef struct { int on, edge, dst, type; float pos, v; } Car;
typedef struct { char t[72]; float clk; Color c; } Feed;

static const Rectangle R_MAP = {28, 204, 780, 566}, R_CHART = {828, 204, 424, 190};
static const Rectangle R_HOT = {828, 410, 424, 190}, R_FEED = {828, 616, 424, 154};
static const char *KPI_N[5] = {"Vehicles", "Avg. speed", "Congestion", "Delay today", "CO2 today"};

static Font fR, fB;
static Node N[NN];
static Edge E[NE];
static int nE, eid[NN][NN], nxt[NN][NN], border[NN], nBorder;
static Car cars[NCAR];
static Feed feed[NFEED];
static Vector2 drops[NDROP];
/* 3D view state */
static RenderTexture2D rt3;
static int view3d, followCar = -1, drag3d;
static float camYaw = .35f, camPitch = .75f, camDist = 75, userDist = 75, followDist = 16, cx3, cy3;
static Vector3 camT, drops3[110];
static float bh[GR - 1][GC - 1][4];
static int bcol[GR - 1][GC - 1][4];
static int paused, speedIdx, rain, greenWave, trips, lastDay;
static float simT, clockS = 6.5f * 3600, spawnAcc, stadiumT, refT, introT, toastT;
static float kpiT[5], kpiD[5], kpiRef[5], delayRate, co2Rate, delayH, co2T;
static const char *toastMsg = "";
static struct { int on; char a[64], b[64]; Vector2 p; Color c; } tip;

/* ---------- helpers ---------- */
static float rnd(void) { return GetRandomValue(0, 10000) / 10000.0f; }
static float Appr(float c, float t, float r, float dt) { return c + (t - c) * fminf(1.0f, r * dt); }
static float G(float h, float m, float s) { float d = h - m; return expf(-d * d / (2 * s * s)); }
static Color Mix(Color a, Color b, float t) {
  t = Clamp(t, 0, 1);
  return (Color){(unsigned char)(a.r + (b.r - a.r) * t), (unsigned char)(a.g + (b.g - a.g) * t),
                 (unsigned char)(a.b + (b.b - a.b) * t), (unsigned char)(a.a + (b.a - a.a) * t)};
}
static void Txt(const char *s, float x, float y, float sz, Color c, int bold, int al) {
  Font f = bold ? fB : fR; float sp = sz * 0.01f; Vector2 m = MeasureTextEx(f, s, sz, sp);
  if (al == AC) x -= m.x / 2; else if (al == AR) x -= m.x;
  DrawTextEx(f, s, (Vector2){floorf(x), floorf(y)}, sz, sp, c);
}
static float TW(const char *s, float sz, int bold) { return MeasureTextEx(bold ? fB : fR, s, sz, sz * 0.01f).x; }
static void RR(Rectangle r, float rad, Color c) {
  float k = rad / (fminf(r.width, r.height) / 2); if (k > 1) k = 1;
  DrawRectangleRounded(r, k, 10, c);
}
static int Hover(Rectangle r) { return CheckCollisionPointRec(GetMousePosition(), r); }
static void Card(Rectangle r, Color border) {
  RR((Rectangle){r.x - 1, r.y - 1, r.width + 2, r.height + 2}, 17, border);
  RR(r, 16, C_CARD);
}
/* Soft radial glow built from stacked translucent circles (avoids DrawCircleGradient, whose signature differs between raylib versions) */
static void Glow(float x, float y, float rad, Color c, float peak) {
  for (int i = 0; i < 14; i++) DrawCircleV((Vector2){x, y}, rad * (1 - i / 14.0f), Fade(c, peak / 14));
}
static void SetTip(const char *a, const char *b, Vector2 p, Color c) {
  tip.on = 1; snprintf(tip.a, 64, "%s", a); snprintf(tip.b, 64, "%s", b); tip.p = p; tip.c = c;
}
static void NName(int n, char *o) { snprintf(o, 8, "%c%d", 'A' + n / GC, n % GC + 1); }
static Vector2 NP(int n) { return (Vector2){N[n].x, N[n].y}; }
static void Toast(const char *m) { toastMsg = m; toastT = 3.0f; }
static void AddFeed(const char *t, Color c) {
  memmove(feed + 1, feed, (NFEED - 1) * sizeof(Feed));
  snprintf(feed[0].t, 72, "%s", t); feed[0].clk = clockS; feed[0].c = c;
}
static float SegD(Vector2 p, Vector2 a, Vector2 b) {
  Vector2 ab = Vector2Subtract(b, a);
  float t = Clamp(Vector2DotProduct(Vector2Subtract(p, a), ab) / Vector2DotProduct(ab, ab), 0, 1);
  return Vector2Distance(p, Vector2Add(a, Vector2Scale(ab, t)));
}

/* ---------- network, routing, signals ---------- */
static void AddRoad(int a, int b, int horiz, int art) {
  float len = Vector2Distance(NP(a), NP(b)), ux = (N[b].x - N[a].x) / len, uy = (N[b].y - N[a].y) / len;
  E[nE] = (Edge){a, b, horiz, art, 0, 0, len, art ? V_ART : V_LOC, 0, 1, ux, uy, 0};
  E[nE + 1] = (Edge){b, a, horiz, art, 0, 0, len, art ? V_ART : V_LOC, 0, 1, -ux, -uy, 0};
  eid[a][b] = nE; eid[b][a] = nE + 1; nE += 2;
}
static void Route(void) { /* Floyd-Warshall on travel time; closed/crashed roads get heavy weights */
  static float d[NN][NN];
  for (int i = 0; i < NN; i++) for (int j = 0; j < NN; j++) { d[i][j] = i == j ? 0 : 1e9f; nxt[i][j] = -1; }
  for (int e = 0; e < nE; e++) {
    float w = E[e].len / E[e].limit;
    if (E[e].closed) w = 1e6f; else if (E[e].crash > 0) w *= 8;
    else if (E[e].works > 0) w *= 3;
    if (w < d[E[e].a][E[e].b]) { d[E[e].a][E[e].b] = w; nxt[E[e].a][E[e].b] = E[e].b; }
  }
  for (int k = 0; k < NN; k++) for (int i = 0; i < NN; i++) for (int j = 0; j < NN; j++)
    if (d[i][k] + d[k][j] < d[i][j]) { d[i][j] = d[i][k] + d[k][j]; nxt[i][j] = nxt[i][k]; }
}
static int Sig(int n, int horiz) { /* 0 red, 1 green, 2 amber */
  float cy = N[n].cycle, t = fmodf(simT + N[n].off, cy), half = cy * .5f;
  int hp = t < half; float rem = hp ? half - t : cy - t;
  if (horiz != hp) return 0;
  return rem < 1.2f ? 2 : 1;
}
static void SetWave(void) {
  for (int i = 0; i < NN; i++) N[i].off = greenWave ? (i % GC) * 5.0f : rnd() * N[i].cycle;
}

/* ---------- simulation ---------- */
static void Spawn(void) {
  int s = border[GetRandomValue(0, nBorder - 1)], d, nn, e, slot = -1;
  d = (stadiumT > 0 && rnd() < .7f) ? GC + 4 : border[GetRandomValue(0, nBorder - 1)];
  if (d == s) return;
  nn = nxt[s][d]; if (nn < 0) return;
  e = eid[s][nn];
  for (int i = 0; i < NCAR; i++) {
    if (!cars[i].on) { if (slot < 0) slot = i; }
    else if (cars[i].edge == e && cars[i].pos < 14) return;
  }
  if (slot < 0) return;
  { float r = rnd(); cars[slot] = (Car){1, e, d, r < .12f ? 2 : r < .3f ? 1 : 0, 0, E[e].limit * .6f}; }
}
static int CrashOn(void) { for (int e = 0; e < nE; e++) if (E[e].crash > 0) return 1; return 0; }
static void StartCrash(int e) {
  char a[8], b[8], t[72];
  if (E[e].crash > 0) { E[e].crash = 0; Route(); AddFeed("Crash cleared", C_GREEN); Toast("Crash cleared"); return; }
  if (E[e].closed) { Toast("That road is closed"); return; }
  E[e].crash = 40; Route();
  NName(E[e].a, a); NName(E[e].b, b); snprintf(t, 72, "Crash on %s > %s", a, b);
  AddFeed(t, C_RED); Toast("Crash reported! Rerouting traffic");
}
static void DoCrash(void) { /* adds one more crash on a random busy road */
  for (int k = 0; k < 60; k++) { int c = GetRandomValue(0, nE - 1); if (E[c].cnt > 0 && !E[c].closed && E[c].crash <= 0) { StartCrash(c); return; } }
}
static void DoStadium(void) {
  if (stadiumT > 0) { stadiumT = 0; AddFeed("Stadium event ended early", C_GREEN); Toast("Stadium event ended"); return; }
  stadiumT = 90; AddFeed("Stadium event: heavy traffic to B5", C_VIOLET); Toast("Stadium event - everyone is heading to B5"); }
static void DoRain(void) {
  rain = !rain; AddFeed(rain ? "Rain started: speeds drop" : "Rain cleared", C_CYAN); Toast(rain ? "Rain rolling in" : "Skies clearing");
}
static int WorksOn(void) { for (int e = 0; e < nE; e += 2) if (E[e].works > 0) return 1; return 0; }
static void StartWorks(int e) {
  char a[8], b[8], t[72]; e &= ~1;
  if (E[e].works > 0) { E[e].works = E[e + 1].works = 0; Route(); AddFeed("Roadworks removed", C_GREEN); Toast("Roadworks removed"); return; }
  if (E[e].closed) { Toast("Can't place roadworks on a closed road"); return; }
  E[e].works = E[e + 1].works = 120; Route();
  NName(E[e].a, a); NName(E[e].b, b); snprintf(t, 72, "Roadworks on %s - %s (slow zone)", a, b);
  AddFeed(t, C_AMBER); Toast("Roadworks started - expect delays");
}
static void DoWorks(void) {
  for (int k = 0; k < 60; k++) { int c = GetRandomValue(0, nE / 2 - 1) * 2; if (!E[c].closed && E[c].works <= 0 && E[c].crash <= 0) { StartWorks(c); return; } }
}
static void ClearIncidents(void) {
  if (!CrashOn() && !WorksOn()) return;
  for (int e = 0; e < nE; e++) E[e].crash = E[e].works = 0;
  Route(); AddFeed("All crashes and roadworks cleared", C_GREEN); Toast("All incidents cleared");
}
static void SimStep(float dt) {
  float h, demand, rs[NE] = {0}, qraw[NN] = {0}, sumV = 0, sumDelay = 0, sumG = 0, dtc = dt * CLOCKX; int rc[NE] = {0}, cnt = 0;
  simT += dt; clockS += dtc; if (stadiumT > 0) stadiumT -= dt;
  { int dn = (int)(clockS / 86400); if (dn != lastDay) { lastDay = dn; delayH = co2T = 0; AddFeed("New day: daily totals reset", C_CYAN); } }
  for (int e = 0; e < nE; e++) if (E[e].crash > 0) {
    E[e].crash -= dt;
    if (E[e].crash <= 0) { E[e].crash = 0; Route(); AddFeed("Crash cleared, flow recovering", C_GREEN); }
  }
  for (int e = 0; e < nE; e += 2) if (E[e].works > 0) {
    E[e].works -= dt; E[e + 1].works = E[e].works;
    if (E[e].works <= 0) { E[e].works = E[e + 1].works = 0; Route(); AddFeed("Roadworks finished, full speed restored", C_GREEN); }
  }
  h = fmodf(clockS / 3600, 24);
  demand = 2.0f * (.22f + G(h, 8, 1.3f) + .9f * G(h, 17.5f, 1.5f) + .3f * G(h, 13, 2.5f)) * (rain ? 1.08f : 1) * (stadiumT > 0 ? 1.7f : 1);
  spawnAcc += demand * dt; while (spawnAcc >= 1) { spawnAcc -= 1; Spawn(); }
  for (int i = 0; i < NCAR; i++) {
    Car *c = &cars[i]; Edge *e; int n, nn = -1, ne = -1, atDst, blocked = 0;
    float gap = 1e9f, vmax, sl, tg, ratio;
    if (!c->on) continue;
    e = &E[c->edge]; n = e->b; atDst = (n == c->dst);
    for (int j = 0; j < NCAR; j++)
      if (j != i && cars[j].on && cars[j].edge == c->edge && cars[j].pos > c->pos) { float g = cars[j].pos - c->pos - 7; if (g < gap) gap = g; }
    if (!atDst) {
      nn = nxt[n][c->dst]; if (nn < 0) { c->on = 0; continue; }
      ne = eid[n][nn]; sl = e->len - c->pos;
      if (Sig(n, e->horiz) != 1) blocked = 1;
      if (sl < 24) for (int j = 0; j < NCAR; j++) if (cars[j].on && cars[j].edge == ne && cars[j].pos < 12) { blocked = 1; break; }
    }
    sl = e->len - c->pos;
    if (blocked && sl - 1 < gap) gap = sl - 1;
    vmax = e->limit * (c->type == 2 ? .8f : c->type == 1 ? .92f : 1) * (rain ? .82f : 1) * (e->crash > 0 ? .12f : 1) * (e->works > 0 ? .4f : 1);
    tg = fminf(vmax, 2.2f * fmaxf(0, gap - 4));
    c->v += Clamp(tg - c->v, -80 * dt, 25 * dt); if (c->v < 0) c->v = 0;
    c->pos += c->v * PXK * dt;
    if (c->pos >= e->len) {
      if (atDst) { c->on = 0; trips++; continue; }
      if (!blocked) { c->pos -= e->len; c->edge = ne; e = &E[ne]; } else c->pos = e->len;
    }
    ratio = fminf(1, c->v / e->limit);
    rs[c->edge] += ratio; rc[c->edge]++; cnt++;
    sumV += c->v; sumDelay += 1 - ratio; sumG += c->v < 5 ? .8f : .4f + .037f * c->v;
    if (c->v < 6 && e->len - c->pos < 50) qraw[e->b] += 1;
  }
  for (int e = 0; e < nE; e++) { E[e].ratio = Appr(E[e].ratio, rc[e] ? rs[e] / rc[e] : 1, 4, dt); E[e].cnt = rc[e]; }
  for (int n = 0; n < NN; n++) N[n].q = Appr(N[n].q, qraw[n], 3, dt);
  delayH += sumDelay * dtc / 3600; co2T += sumG * dtc / 1e6f; delayRate = sumDelay; co2Rate = sumG * 3.6f;
  kpiT[0] = (float)cnt; kpiT[1] = cnt ? sumV / cnt : 40; kpiT[2] = cnt ? sumDelay / cnt * 100 : 0; kpiT[3] = delayH; kpiT[4] = co2T;
  refT += dt; if (refT >= 30) { refT = 0; memcpy(kpiRef, kpiT, sizeof kpiT); }
}

/* ---------- drawing ---------- */
static Color SigCol(int s) { return s == 1 ? C_GREEN : s == 2 ? C_AMBER : C_RED; }

static void DrawHeader(void) {
  float pulse = .5f + .5f * sinf((float)GetTime() * 4); char b[16]; int act = (int)(GetTime() * .8) % 3;
  int hh = (int)(fmodf(clockS, 86400) / 3600), mm = (int)(fmodf(clockS, 3600) / 60);
  Color lc = paused ? C_AMBER : C_GREEN, lamp[3] = {C_RED, C_AMBER, C_GREEN}, ec[4] = {C_PINK, C_VIOLET, C_CYAN, C_AMBER};
  Rectangle pill = {250, 28, paused ? 100 : 84, 28}, tc = {1076, 22, 176, 40};
  static const char *EV[4] = {"Crash", "Stadium", "Rain", "Works"}, *SP[3] = {"1x", "2x", "4x"};
  RR((Rectangle){28, 22, 40, 40}, 12, C_VIOLET); RR((Rectangle){39, 27, 18, 30}, 7, C_BG);
  for (int i = 0; i < 3; i++) DrawCircleV((Vector2){48, 34.0f + i * 8}, 3.4f, Fade(lamp[i], i == act ? 1.0f : .22f));
  Txt("Gridlock", 80, 17, 26, C_TEXT, 1, AL); Txt("City traffic monitor", 80, 46, 13, C_MUTED, 0, AL);
  RR(pill, 14, Fade(lc, .14f)); DrawCircleV((Vector2){pill.x + 16, pill.y + 14}, 3.5f, lc);
  DrawRing((Vector2){pill.x + 16, pill.y + 14}, 5 + pulse * 3, 6 + pulse * 3, 0, 360, 24, Fade(lc, .5f * (1 - pulse)));
  Txt(paused ? "PAUSED" : "LIVE", pill.x + 30, pill.y + 7, 12, lc, 1, AL);
  snprintf(b, 16, "%02d:%02d", hh, mm); Txt(b, 520, 12, 30, C_TEXT, 1, AC);
  Txt(stadiumT > 0 ? (rain ? "Rain + stadium event" : "Stadium event") : (rain ? "Rain" : "Clear skies"), 520, 46, 12, C_MUTED, 0, AC);
  for (int i = 0; i < 4; i++) {
    Rectangle r = {696 + i * 94, 22, 86, 40}; int on = (i == 0 && CrashOn()) || (i == 2 && rain) || (i == 1 && stadiumT > 0) || (i == 3 && WorksOn());
    RR(r, 20, Hover(r) || on ? ec[i] : Fade(ec[i], .18f)); Txt(EV[i], r.x + 43, r.y + 11, 15, Hover(r) || on ? WHITE : ec[i], 1, AC);
  }
  RR((Rectangle){tc.x - 1, tc.y - 1, tc.width + 2, tc.height + 2}, 21, C_BORDER); RR(tc, 20, C_CARD);
  for (int i = 0; i < 3; i++) {
    Rectangle t = {tc.x + 4 + i * 56, 26, 56, 32};
    if (i == speedIdx) RR(t, 16, C_VIOLET); else if (Hover(t)) RR(t, 16, Fade(WHITE, .06f));
    Txt(SP[i], t.x + 28, t.y + 8, 15, i == speedIdx ? WHITE : C_MUTED, i == speedIdx, AC);
  }
}

static void DrawKpi(int i) {
  Rectangle r = {28 + i * 248, 88, 232, 100}; Color ac[5] = {C_CYAN, C_GREEN, C_PINK, C_AMBER, C_VIOLET}, pc;
  char b[48], p[32]; const char *sub; Rectangle pill; float v = kpiD[i], d = kpiRef[i] > 0.001f ? (kpiT[i] - kpiRef[i]) / kpiRef[i] * 100 : 0;
  Card(r, Hover(r) ? Fade(ac[i], .75f) : C_BORDER);
  Txt(KPI_N[i], r.x + 20, r.y + 16, 13, C_MUTED, 0, AL);
  if (i == 0) snprintf(b, 48, "%.0f", v); else if (i == 1) snprintf(b, 48, "%.0f km/h", v); else if (i == 2) snprintf(b, 48, "%.0f%%", v);
  else if (i == 3) snprintf(b, 48, "%.1f veh-h", v); else snprintf(b, 48, "%.2f t", v);
  Txt(b, r.x + 20, r.y + 34, 30, C_TEXT, 1, AL);
  if (i < 3) { snprintf(p, 32, "%+.1f%%", d); sub = "vs 30s ago"; pc = i == 0 ? C_CYAN : ((i == 1) == (d >= 0) ? C_GREEN : C_PINK); }
  else { snprintf(p, 32, i == 3 ? "%.0f veh-h/h" : "%.0f kg/h", i == 3 ? delayRate : co2Rate); sub = "right now"; pc = C_AMBER; }
  pill = (Rectangle){r.x + 20, r.y + 72, TW(p, 12, 1) + 20, 20}; RR(pill, 10, Fade(pc, .15f));
  Txt(p, pill.x + 10, pill.y + 3, 12, pc, 1, AL); Txt(sub, pill.x + pill.width + 8, pill.y + 4, 11, C_MUTED, 0, AL);
}

static void DrawMap(int hn, int he) {
  Rectangle r = R_MAP; float day = Clamp(sinf((fmodf(clockS / 3600, 24) - 6) / 12 * PI), 0, 1), dtm = GetFrameTime(); char b[48], t[8];
  Card(r, C_BORDER); RR((Rectangle){r.x + 6, r.y + 6, r.width - 12, r.height - 12}, 12, Mix((Color){13, 16, 31, 255}, (Color){26, 32, 56, 255}, day));
  Txt("CITY DISTRICT", r.x + 24, r.y + 18, 12, C_MUTED, 1, AL);
  Txt("click: close/open   ctrl+click: roadworks   shift+click: crash   scroll junction: retime", r.x + r.width - 24, r.y + 18, 12, C_MUTED, 0, AR);
  { char l[32]; float ly = r.y + r.height - 26;
    DrawLineEx((Vector2){r.x + 24, ly}, (Vector2){r.x + 52, ly}, 9, C_ART); DrawLineEx((Vector2){r.x + 28, ly}, (Vector2){r.x + 48, ly}, 1.5f, Fade(WHITE, .35f));
    snprintf(l, 32, "Arterial %.0f km/h", V_ART); Txt(l, r.x + 60, ly - 7, 12, C_MUTED, 0, AL);
    DrawLineEx((Vector2){r.x + 200, ly}, (Vector2){r.x + 228, ly}, 6, C_ROAD);
    snprintf(l, 32, "Local %.0f km/h", V_LOC); Txt(l, r.x + 236, ly - 7, 12, C_MUTED, 0, AL); }
  for (int i = 0; i < GR; i++) { snprintf(t, 8, "%c", 'A' + i); Txt(t, r.x + 24, N[i * GC].y - 8, 13, C_MUTED, 1, AL); }
  for (int i = 0; i < GC; i++) { snprintf(t, 8, "%d", i + 1); Txt(t, N[i].x, r.y + 38, 13, C_MUTED, 1, AC); }
  for (int e = 0; e < nE; e += 2) {
    Color base = E[e].art ? C_ART : C_ROAD, rc = E[e].closed ? Mix(base, C_RED, .35f) : base; Vector2 a = NP(E[e].a), u = {E[e].ux, E[e].uy};
    DrawLineEx(a, NP(E[e].b), E[e].art ? 17 : 12, rc);
    if (E[e].art) for (float d = 16; d + 7 < E[e].len - 14; d += 14) DrawLineEx(Vector2Add(a, Vector2Scale(u, d)), Vector2Add(a, Vector2Scale(u, d + 7)), 1.5f, Fade(WHITE, .3f));
  }
  for (int e = 0; e < nE; e++) {
    float rt = E[e].ratio; Vector2 a = NP(E[e].a), n = {-E[e].uy * 3.6f, E[e].ux * 3.6f};
    Color cc = rt > .6f ? Mix(C_AMBER, C_GREEN, (rt - .6f) / .4f) : Mix(C_RED, C_AMBER, rt / .6f);
    Vector2 p0 = {a.x + E[e].ux * 13 + n.x, a.y + E[e].uy * 13 + n.y}, p1 = {a.x + E[e].ux * (E[e].len - 13) + n.x, a.y + E[e].uy * (E[e].len - 13) + n.y};
    DrawLineEx(p0, p1, 3, E[e].closed ? Fade(C_MUTED, .25f) : Fade(cc, .7f));
  }
  for (int e = 0; e < nE; e += 2) {
    Vector2 m = Vector2Lerp(NP(E[e].a), NP(E[e].b), .5f);
    if (E[e].closed) { DrawLineEx((Vector2){m.x - 6, m.y - 6}, (Vector2){m.x + 6, m.y + 6}, 3, C_RED); DrawLineEx((Vector2){m.x - 6, m.y + 6}, (Vector2){m.x + 6, m.y - 6}, 3, C_RED); }
  }
  for (int e = 0; e < nE; e++) if (E[e].crash > 0) {
    Vector2 m = Vector2Lerp(NP(E[e].a), NP(E[e].b), .5f); int f = sinf((float)GetTime() * 12) > 0;
    DrawCircleV(m, 16, Fade(f ? C_RED : C_CYAN, .22f)); DrawCircleV(m, 5, f ? C_RED : C_CYAN); DrawCircleV(m, 2, WHITE);
  }
  for (int e = 0; e < nE; e += 2) if (E[e].works > 0) {
    Vector2 a = NP(E[e].a), u = {E[e].ux, E[e].uy}; float pu = .5f + .5f * sinf((float)GetTime() * 5);
    DrawLineEx(Vector2Add(a, Vector2Scale(u, 18)), Vector2Add(a, Vector2Scale(u, E[e].len - 18)), 16, Fade(C_AMBER, .10f + .08f * pu));
    for (int k = 0; k < 6; k++) {
      Vector2 p = Vector2Add(a, Vector2Scale(u, 26 + k * (E[e].len - 52) / 5));
      DrawTriangle((Vector2){p.x, p.y - 6}, (Vector2){p.x - 4, p.y + 3}, (Vector2){p.x + 4, p.y + 3}, (Color){255, 120, 30, 255});
      DrawLineEx((Vector2){p.x - 2.2f, p.y - .5f}, (Vector2){p.x + 2.2f, p.y - .5f}, 1.6f, WHITE);
    }
  }
  for (int i = 0; i < NN; i++) {
    Vector2 p = NP(i); int sh = Sig(i, 1), sv = Sig(i, 0);
    DrawCircleV(p, 11, (Color){22, 26, 46, 255});
    DrawCircleV((Vector2){p.x - 6, p.y}, 2.6f, SigCol(sh)); DrawCircleV((Vector2){p.x + 6, p.y}, 2.6f, SigCol(sh));
    DrawCircleV((Vector2){p.x, p.y - 6}, 2.6f, SigCol(sv)); DrawCircleV((Vector2){p.x, p.y + 6}, 2.6f, SigCol(sv));
    if (i == hn) DrawRing(p, 14, 16, 0, 360, 32, Fade(WHITE, .6f));
  }
  for (int i = 0; i < NCAR; i++) if (cars[i].on) {
    Edge *e = &E[cars[i].edge]; Vector2 a = NP(e->a), p = {a.x + e->ux * cars[i].pos - e->uy * 3.6f, a.y + e->uy * cars[i].pos + e->ux * 3.6f};
    Color c = Mix(C_PINK, C_CYAN, cars[i].v / e->limit); float rad = cars[i].type == 2 ? 3.8f : cars[i].type == 1 ? 3.0f : 2.4f;
    DrawCircleV(p, rad * 2.3f, Fade(c, .12f)); DrawCircleV(p, rad, c);
  }
  { Vector2 sp = NP(GC + 4); float pu = .5f + .5f * sinf((float)GetTime() * 4);
    if (stadiumT > 0) {
      float rem = stadiumT * CLOCKX, endc = fmodf(clockS + rem, 86400), w; char l2[48];
      DrawCircleV(sp, 20 + pu * 5, Fade(C_VIOLET, .16f));
      DrawRing(sp, 17, 19.5f, 0, 360, 48, Fade(C_VIOLET, .35f));
      DrawRing(sp, 17, 19.5f, -90, -90 + 360 * (stadiumT / 90.0f), 48, C_VIOLET);
      snprintf(l2, 48, "ends %02d:%02d  (%d min left)", (int)(endc / 3600), (int)(fmodf(endc, 3600) / 60), (int)ceilf(rem / 60));
      w = fmaxf(TW("STADIUM EVENT", 11, 1), TW(l2, 11, 0)) + 20;
      RR((Rectangle){sp.x + 24, sp.y - 44, w, 38}, 8, (Color){28, 20, 58, 235});
      Txt("STADIUM EVENT", sp.x + 34, sp.y - 39, 11, C_VIOLET, 1, AL); Txt(l2, sp.x + 34, sp.y - 22, 11, C_TEXT, 0, AL);
    } else { DrawRing(sp, 15, 16.5f, 0, 360, 32, Fade(C_VIOLET, .45f)); Txt("stadium", sp.x, sp.y + 17, 10, Fade(C_VIOLET, .8f), 0, AC); }
  }
  if (rain) for (int i = 0; i < NDROP; i++) {
    drops[i].y += 420 * dtm; drops[i].x -= 80 * dtm;
    if (drops[i].y > r.y + r.height - 10) { drops[i].y = r.y + 8; drops[i].x = r.x + rnd() * r.width; }
    if (drops[i].x < r.x + 8) drops[i].x = r.x + r.width - 8;
    DrawLineEx(drops[i], (Vector2){drops[i].x - 2, drops[i].y + 8}, 1.2f, Fade(C_CYAN, .3f));
  }
  if (hn >= 0) { NName(hn, t); snprintf(b, 48, "cycle %.0fs, %.0f waiting", N[hn].cycle, N[hn].q); SetTip(t, b, NP(hn), C_AMBER); }
  else if (he >= 0) {
    char a[8], c[8], l[64]; NName(E[he].a, a); NName(E[he].b, c); snprintf(l, 64, "%s - %s", a, c);
    if (E[he].closed) snprintf(b, 48, "CLOSED - click to reopen");
    else if (E[he].works > 0) snprintf(b, 48, "Roadworks - %d min left", (int)ceilf(E[he].works * CLOCKX / 60));
    else snprintf(b, 48, "%.0f km/h, %d cars (%s)", E[he].ratio * E[he].limit, E[he].cnt + E[he ^ 1].cnt, E[he].art ? "arterial" : "local");
    SetTip(l, b, GetMousePosition(), E[he].closed ? C_RED : E[he].works > 0 ? C_AMBER : C_CYAN);
  }
}

typedef struct { Color c; char t[40], d[40]; float frac; } Ev;
static void PushEv(Ev *l, int *n, int *over, Color c, const char *t, const char *d, float frac) {
  if (*n >= 5) { (*over)++; return; }
  l[*n].c = c; snprintf(l[*n].t, 40, "%s", t); snprintf(l[*n].d, 40, "%s", d); l[*n].frac = frac; (*n)++;
}
static void DrawEvents(void) {
  Rectangle r = R_CHART; Ev ev[5]; int n = 0, over = 0, closed = 0; char t[40], d[40], a[8], b[8];
  if (stadiumT > 0) {
    float rem = stadiumT * CLOCKX, endc = fmodf(clockS + rem, 86400);
    snprintf(d, 40, "%d min left (ends %02d:%02d)", (int)ceilf(rem / 60), (int)(endc / 3600), (int)(fmodf(endc, 3600) / 60));
    PushEv(ev, &n, &over, C_VIOLET, "Stadium event at B5", d, stadiumT / 90.0f);
  }
  for (int e = 0; e < nE; e++) if (E[e].crash > 0) {
    NName(E[e].a, a); NName(E[e].b, b); snprintf(t, 40, "Crash on %s > %s", a, b); snprintf(d, 40, "clears in %d min", (int)ceilf(E[e].crash * CLOCKX / 60));
    PushEv(ev, &n, &over, C_RED, t, d, E[e].crash / 40.0f);
  }
  for (int e = 0; e < nE; e += 2) if (E[e].works > 0) {
    NName(E[e].a, a); NName(E[e].b, b); snprintf(t, 40, "Roadworks %s - %s", a, b); snprintf(d, 40, "%d min left", (int)ceilf(E[e].works * CLOCKX / 60));
    PushEv(ev, &n, &over, C_AMBER, t, d, E[e].works / 120.0f);
  }
  for (int e = 0; e < nE; e += 2) if (E[e].closed) closed++;
  if (closed) { snprintf(t, 40, "%d road%s closed", closed, closed > 1 ? "s" : ""); PushEv(ev, &n, &over, C_PINK, t, "click to reopen", -1); }
  if (rain) PushEv(ev, &n, &over, C_CYAN, "Rain", "speeds -18%, demand +8%", -1);
  if (greenWave) PushEv(ev, &n, &over, C_GREEN, "Green wave", "signals coordinated", -1);
  Card(r, C_BORDER); Txt("ACTIVE EVENTS", r.x + 24, r.y + 18, 12, C_MUTED, 1, AL);
  if (n) { snprintf(d, 40, "%d ACTIVE", n + over); Txt(d, r.x + r.width - 24, r.y + 18, 12, C_AMBER, 1, AR); }
  else {
    DrawRing((Vector2){r.x + r.width / 2, r.y + 80}, 16, 18, 0, 360, 40, Fade(C_GREEN, .6f)); DrawCircleV((Vector2){r.x + r.width / 2, r.y + 80}, 5, C_GREEN);
    Txt("All quiet", r.x + r.width / 2, r.y + 108, 18, C_TEXT, 1, AC);
    Txt("Press C, S, R or W to trigger an event", r.x + r.width / 2, r.y + 134, 12, C_MUTED, 0, AC);
  }
  for (int i = 0; i < n; i++) {
    float y = r.y + 46 + i * 28;
    RR((Rectangle){r.x + 24, y, 4, 17}, 2, ev[i].c);
    Txt(ev[i].t, r.x + 38, y - 1, 13, C_TEXT, 1, AL); Txt(ev[i].d, r.x + r.width - 24, y, 12, C_MUTED, 0, AR);
    if (ev[i].frac >= 0) { RR((Rectangle){r.x + 38, y + 19, r.width - 62, 3}, 1.5f, Fade(WHITE, .07f)); RR((Rectangle){r.x + 38, y + 19, fmaxf(3, (r.width - 62) * ev[i].frac), 3}, 1.5f, ev[i].c); }
  }
}

static void DrawHot(void) {
  Rectangle r = R_HOT; int idx[NN]; char b[48], nm[8]; float mq = 4;
  Card(r, C_BORDER); Txt("JUNCTION QUEUES", r.x + 24, r.y + 18, 12, C_MUTED, 1, AL); Txt("cars waiting", r.x + r.width - 24, r.y + 18, 12, C_MUTED, 0, AR);
  for (int i = 0; i < NN; i++) idx[i] = i;
  for (int i = 0; i < 6; i++) for (int j = i + 1; j < NN; j++) if (N[idx[j]].q > N[idx[i]].q) { int t = idx[i]; idx[i] = idx[j]; idx[j] = t; }
  for (int i = 0; i < 6; i++) mq = fmaxf(mq, N[idx[i]].q);
  for (int i = 0; i < 6; i++) {
    float y = r.y + 46 + i * 23, q = N[idx[i]].q, w = r.width - 140; Color c = Mix(C_GREEN, C_PINK, q / 9);
    NName(idx[i], nm); Txt(nm, r.x + 24, y, 13, C_TEXT, 1, AL);
    RR((Rectangle){r.x + 60, y + 4, w, 8}, 4, Fade(WHITE, .06f)); RR((Rectangle){r.x + 60, y + 4, fmaxf(8, w * q / (mq * 1.1f)), 8}, 4, c);
    snprintf(b, 48, "%.0f", q); Txt(b, r.x + r.width - 24, y, 13, C_TEXT, 1, AR);
  }
}

static void DrawFeed(void) {
  Rectangle r = R_FEED; char b[16];
  Card(r, C_BORDER); Txt("INCIDENTS & EVENTS", r.x + 24, r.y + 18, 12, C_MUTED, 1, AL);
  for (int i = 0; i < NFEED; i++) if (feed[i].t[0]) {
    float y = r.y + 44 + i * 21; float a = 1 - i * .15f;
    snprintf(b, 16, "%02d:%02d", (int)(fmodf(feed[i].clk, 86400) / 3600), (int)(fmodf(feed[i].clk, 3600) / 60));
    Txt(b, r.x + 24, y, 12, Fade(C_MUTED, a), 0, AL); DrawCircleV((Vector2){r.x + 80, y + 8}, 3.5f, Fade(feed[i].c, a)); Txt(feed[i].t, r.x + 94, y - 1, 13, Fade(C_TEXT, a), 0, AL);
  }
}

static void DrawOverlay(void) {
  if (toastT > 0) {
    float a = Clamp(fminf(toastT, 3.0f - toastT) * 4, 0, 1), w = TW(toastMsg, 15, 1) + 64; Rectangle t = {SW / 2 - w / 2, 66 - 60 * (1 - a), w, 38};
    RR((Rectangle){t.x, t.y + 3, w, 38}, 19, Fade(BLACK, .35f)); RR(t, 19, Mix(C_PINK, C_VIOLET, .4f));
    DrawCircleV((Vector2){t.x + 22, t.y + 19}, 4, WHITE); Txt(toastMsg, t.x + 38, t.y + 10, 15, WHITE, 1, AL);
  }
  if (tip.on) {
    float w = fmaxf(TW(tip.a, 14, 1), TW(tip.b, 12, 0)) + 34, h = 50, x = tip.p.x + 16, y = tip.p.y - h - 12;
    if (x + w > SW - 8) x = tip.p.x - w - 16;
    if (y < 8) y = tip.p.y + 18;
    RR((Rectangle){x, y + 4, w, h}, 10, Fade(BLACK, .4f)); RR((Rectangle){x - 1, y - 1, w + 2, h + 2}, 11, C_BORDER); RR((Rectangle){x, y, w, h}, 10, (Color){28, 33, 58, 250});
    RR((Rectangle){x + 11, y + 11, 3, h - 22}, 1.5f, tip.c); Txt(tip.a, x + 22, y + 9, 14, C_TEXT, 1, AL); Txt(tip.b, x + 22, y + 28, 12, C_MUTED, 0, AL);
  }
}

/* ---------- 3D view ---------- */
static Vector3 W3(float px, float py, float y) { return (Vector3){(px - cx3) / 10.0f, y, (py - cy3) / 10.0f}; }

static void UpdateCam3D(float dt) {
  if (followCar >= 0 && !cars[followCar].on) {
    int old = followCar; followCar = -1;
    for (int k = 0; k < 60; k++) { int c = GetRandomValue(0, NCAR - 1); if (cars[c].on && c != old) { followCar = c; break; } }
  }
  if (followCar >= 0) {
    Car *c = &cars[followCar]; Edge *e = &E[c->edge]; Vector2 a = NP(e->a);
    Vector3 cp = W3(a.x + e->ux * c->pos, a.y + e->uy * c->pos, .3f);
    float dy = atan2f(-e->ux, -e->uy) - camYaw;
    while (dy > PI) dy -= 2 * PI;
    while (dy < -PI) dy += 2 * PI;
    camT = Vector3Lerp(camT, cp, fminf(1, 8 * dt)); camYaw += dy * fminf(1, 1.8f * dt);
    camPitch = Appr(camPitch, .42f, 2, dt); camDist = Appr(camDist, followDist, 4, dt);
  } else camDist = Appr(camDist, userDist, 6, dt);
}

static void Render3D(void) {
  float day = Clamp(sinf((fmodf(clockS / 3600, 24) - 6) / 12 * PI), 0, 1), t = (float)GetTime(), cp = cosf(camPitch), pulse = .5f + .5f * sinf(t * 4), dtf = GetFrameTime();
  Color sky = Mix((Color){9, 11, 24, 255}, (Color){58, 84, 128, 255}, day), gnd = Mix((Color){17, 20, 36, 255}, (Color){30, 36, 58, 255}, day);
  static const Color BC[5] = {{52, 60, 98, 255}, {62, 54, 104, 255}, {44, 72, 98, 255}, {72, 62, 92, 255}, {56, 80, 112, 255}};
  Camera3D cam = {0}; Node *s0 = &N[GC + 4], *s3 = &N[2 * GC + 5];
  Vector3 sc = W3((s0->x + s3->x) / 2, (s0->y + s3->y) / 2, 0);
  if (rain) { sky = Mix(sky, (Color){70, 76, 92, 255}, .55f); gnd = Mix(gnd, (Color){24, 28, 40, 255}, .5f); }
  cam.position = (Vector3){camT.x + camDist * cp * sinf(camYaw), camT.y + camDist * sinf(camPitch), camT.z + camDist * cp * cosf(camYaw)};
  cam.target = camT; cam.up = (Vector3){0, 1, 0}; cam.fovy = 45; cam.projection = CAMERA_PERSPECTIVE;
  BeginTextureMode(rt3); ClearBackground(sky); BeginMode3D(cam);
  DrawCubeV((Vector3){0, -.06f, 0}, (Vector3){170, .12f, 130}, gnd);
  for (int e = 0; e < nE; e += 2) { /* road surfaces */
    Vector3 m = W3((N[E[e].a].x + N[E[e].b].x) / 2, (N[E[e].a].y + N[E[e].b].y) / 2, .03f); float L = E[e].len / 10, w = E[e].art ? 1.7f : 1.2f;
    Color base = E[e].art ? C_ART : C_ROAD, rc = E[e].closed ? Mix(base, C_RED, .35f) : base;
    DrawCubeV(m, E[e].horiz ? (Vector3){L, .06f, w} : (Vector3){w, .06f, L}, rc);
  }
  for (int i = 0; i < NN; i++) DrawCubeV(W3(N[i].x, N[i].y, .04f), (Vector3){1.9f, .07f, 1.9f}, (Color){36, 42, 70, 255});
  for (int e = 0; e < nE; e++) { /* congestion-coloured lanes */
    float rt = E[e].ratio, L = E[e].len / 10 - 2.6f; Vector2 a = NP(E[e].a), n = {-E[e].uy * 3.6f, E[e].ux * 3.6f};
    Color cc = rt > .6f ? Mix(C_AMBER, C_GREEN, (rt - .6f) / .4f) : Mix(C_RED, C_AMBER, rt / .6f);
    Vector3 m = W3(a.x + E[e].ux * E[e].len / 2 + n.x, a.y + E[e].uy * E[e].len / 2 + n.y, .08f);
    if (E[e].closed) cc = (Color){70, 76, 100, 255};
    DrawCubeV(m, E[e].horiz ? (Vector3){L, .02f, .3f} : (Vector3){.3f, .02f, L}, cc);
  }
  for (int r = 0; r < GR - 1; r++) for (int c = 0; c < GC - 1; c++) { /* buildings */
    Node *n0 = &N[r * GC + c], *n3 = &N[(r + 1) * GC + c + 1];
    float bw = ((n3->x - n0->x) / 10 - 3.2f) / 2, bd = ((n3->y - n0->y) / 10 - 3.2f) / 2; Vector3 mc = W3((n0->x + n3->x) / 2, (n0->y + n3->y) / 2, 0);
    if (r == 1 && c == 4) continue; /* stadium block */
    for (int k = 0; k < 4; k++) {
      float h = bh[r][c][k]; Color col = BC[bcol[r][c][k]];
      Vector3 p = {mc.x + (k % 2 ? 1 : -1) * (bw / 2 + .2f), h / 2, mc.z + (k / 2 ? 1 : -1) * (bd / 2 + .2f)};
      DrawCubeV(p, (Vector3){bw, h, bd}, col); DrawCubeV((Vector3){p.x, h + .04f, p.z}, (Vector3){bw + .1f, .08f, bd + .1f}, Mix(col, WHITE, .25f));
      DrawCubeWiresV(p, (Vector3){bw, h, bd}, Fade(C_CYAN, .22f));
    }
  }
  DrawCylinder(sc, 4.6f, 5.2f, 1.8f, 28, Mix(C_VIOLET, C_BG, .35f)); /* stadium */
  DrawCylinder(sc, 3.6f, 3.6f, 1.86f, 28, (Color){18, 14, 36, 255});
  DrawCylinder(sc, 3.3f, 3.3f, 1.9f, 28, (Color){24, 74, 56, 255});
  for (int k = 0; k < 4; k++) {
    float dx = k % 2 ? 4.3f : -4.3f, dz = k / 2 ? 4.3f : -4.3f;
    DrawCubeV((Vector3){sc.x + dx, 2.6f, sc.z + dz}, (Vector3){.18f, 5.2f, .18f}, (Color){70, 76, 100, 255});
    DrawCubeV((Vector3){sc.x + dx, 5.3f, sc.z + dz}, (Vector3){.7f, .3f, .7f}, stadiumT > 0 ? WHITE : Mix(C_AMBER, WHITE, .3f));
  }
  for (int i = 0; i < NN; i++) { /* traffic lights */
    Color ch = SigCol(Sig(i, 1)), cv = SigCol(Sig(i, 0)); Vector3 p = W3(N[i].x, N[i].y, 0);
    for (int k = 0; k < 4; k++) {
      float sx = k == 0 ? -1.15f : k == 1 ? 1.15f : 0, sz = k == 2 ? -1.15f : k == 3 ? 1.15f : 0;
      DrawCubeV((Vector3){p.x + sx, .25f, p.z + sz}, (Vector3){.07f, .5f, .07f}, (Color){60, 66, 90, 255});
      DrawCubeV((Vector3){p.x + sx, .58f, p.z + sz}, (Vector3){.3f, .3f, .3f}, k < 2 ? ch : cv);
    }
  }
  for (int e = 0; e < nE; e += 2) { /* cones, barriers, crash beacons */
    Vector2 a = NP(E[e].a); Vector3 m = W3(a.x + E[e].ux * E[e].len / 2, a.y + E[e].uy * E[e].len / 2, 0);
    if (E[e].works > 0) for (int k = 0; k < 6; k++) {
      float d = 26 + k * (E[e].len - 52) / 5; DrawCylinder(W3(a.x + E[e].ux * d, a.y + E[e].uy * d, .08f), 0, .24f, .6f, 8, (Color){255, 120, 30, 255});
    }
    if (E[e].closed) DrawCubeV((Vector3){m.x, .5f, m.z}, E[e].horiz ? (Vector3){.25f, 1.0f, 1.6f} : (Vector3){1.6f, 1.0f, .25f}, C_RED);
    if (E[e].crash > 0 || E[e + 1].crash > 0) {
      Color f = sinf(t * 12) > 0 ? C_RED : C_CYAN;
      DrawCubeV((Vector3){m.x, .5f, m.z}, (Vector3){.6f, 1.0f, .6f}, (Color){50, 54, 74, 255}); DrawSphere((Vector3){m.x, 1.5f, m.z}, .45f, f);
    }
  }
  for (int i = 0; i < NCAR; i++) if (cars[i].on) { /* cars */
    Edge *e = &E[cars[i].edge]; Vector2 a = NP(e->a), q = {a.x + e->ux * cars[i].pos - e->uy * 3.6f, a.y + e->uy * cars[i].pos + e->ux * 3.6f};
    float L = cars[i].type == 2 ? 1.9f : cars[i].type == 1 ? 1.2f : .95f, H = cars[i].type == 2 ? .8f : .42f, Wd = cars[i].type == 2 ? .6f : .48f;
    Color c = Mix(C_PINK, C_CYAN, cars[i].v / e->limit); Vector3 p = W3(q.x, q.y, H / 2 + .08f), sz = e->horiz ? (Vector3){L, H, Wd} : (Vector3){Wd, H, L};
    DrawCubeV(p, sz, c); DrawCubeV((Vector3){p.x, p.y + H / 2, p.z}, (Vector3){sz.x * .7f, .14f, sz.z * .7f}, Mix(c, BLACK, .45f));
    if (i == followCar) DrawCubeWiresV(p, (Vector3){sz.x + .3f, sz.y + .3f, sz.z + .3f}, WHITE);
  }
  for (int e = 0; e < nE; e += 2) if (E[e].works > 0) { /* translucent pass (drawn last) */
    Vector2 a = NP(E[e].a); Vector3 m = W3(a.x + E[e].ux * E[e].len / 2, a.y + E[e].uy * E[e].len / 2, .1f); float L = E[e].len / 10 - 3.6f;
    DrawCubeV(m, E[e].horiz ? (Vector3){L, .03f, 1.5f} : (Vector3){1.5f, .03f, L}, Fade(C_AMBER, .22f + .12f * pulse));
  }
  if (stadiumT > 0) DrawCylinder(sc, 3.2f, 4.2f, 12, 24, Fade(C_VIOLET, .10f + .08f * pulse));
  if (rain) for (int i = 0; i < 110; i++) {
    drops3[i].y -= 24 * dtf;
    if (drops3[i].y < 0) drops3[i] = (Vector3){(rnd() - .5f) * 80, 14 + rnd() * 6, (rnd() - .5f) * 60};
    DrawLine3D(drops3[i], (Vector3){drops3[i].x - .1f, drops3[i].y + .9f, drops3[i].z}, Fade(C_CYAN, .4f));
  }
  EndMode3D(); EndTextureMode();
}

static void DrawMap3D(void) {
  Rectangle r = R_MAP;
  Card(r, C_BORDER); Txt("CITY DISTRICT", r.x + 24, r.y + 18, 12, C_MUTED, 1, AL);
  Txt("drag: orbit   right-drag: pan   scroll: zoom   F: follow a car", r.x + r.width - 24, r.y + 18, 12, C_MUTED, 0, AR);
  DrawTexturePro(rt3.texture, (Rectangle){0, 0, (float)rt3.texture.width, -(float)rt3.texture.height}, (Rectangle){r.x + 8, r.y + 44, r.width - 16, r.height - 52}, (Vector2){0, 0}, 0, WHITE);
  if (followCar >= 0) { RR((Rectangle){r.x + 20, r.y + r.height - 44, 230, 26}, 13, (Color){28, 20, 58, 230}); Txt("Following a car - F to stop", r.x + 34, r.y + r.height - 39, 12, C_TEXT, 1, AL); }
}

static void DrawViewToggle(void) {
  Rectangle t = {R_MAP.x + 132, R_MAP.y + 10, 96, 26}; static const char *L[2] = {"2D", "3D"};
  RR((Rectangle){t.x - 1, t.y - 1, t.width + 2, t.height + 2}, 14, C_BORDER); RR(t, 13, C_BG);
  for (int i = 0; i < 2; i++) {
    Rectangle h = {t.x + 3 + i * 45, t.y + 3, 45, 20}; int on = (i == 1) == (view3d != 0);
    if (on) RR(h, 10, C_VIOLET); else if (Hover(h)) RR(h, 10, Fade(WHITE, .06f));
    Txt(L[i], h.x + 22, h.y + 3, 12, on ? WHITE : C_MUTED, on, AC);
  }
}

/* ---------- main ---------- */
static void LoadFonts(void) {
  const char *reg[] = {"fonts/Inter-Regular.ttf", "/usr/share/fonts/truetype/dejavu/DejaVuSans.ttf", "/usr/share/fonts/TTF/DejaVuSans.ttf",
    "C:/Windows/Fonts/segoeui.ttf", "/System/Library/Fonts/Supplemental/Arial.ttf", "/Library/Fonts/Arial.ttf"};
  const char *bld[] = {"fonts/Inter-Bold.ttf", "/usr/share/fonts/truetype/dejavu/DejaVuSans-Bold.ttf", "/usr/share/fonts/TTF/DejaVuSans-Bold.ttf",
    "C:/Windows/Fonts/segoeuib.ttf", "/System/Library/Fonts/Supplemental/Arial Bold.ttf", "/Library/Fonts/Arial Bold.ttf"};
  fR = GetFontDefault();
  for (int i = 0; i < 6; i++) if (FileExists(reg[i])) { fR = LoadFontEx(reg[i], 48, NULL, 0); break; }
  fB = fR;
  for (int i = 0; i < 6; i++) if (FileExists(bld[i])) { fB = LoadFontEx(bld[i], 48, NULL, 0); break; }
  GenTextureMipmaps(&fR.texture); SetTextureFilter(fR.texture, TEXTURE_FILTER_TRILINEAR);
  if (fB.texture.id != fR.texture.id) { GenTextureMipmaps(&fB.texture); SetTextureFilter(fB.texture, TEXTURE_FILTER_TRILINEAR); }
}

int main(void) {
  static const int MULT[3] = {1, 2, 4};
  SetConfigFlags(FLAG_MSAA_4X_HINT | FLAG_VSYNC_HINT);
  InitWindow(SW, SH, "Gridlock - City Traffic Monitor"); SetTargetFPS(60); LoadFonts();
  for (int i = 0; i < NN; i++) for (int j = 0; j < NN; j++) eid[i][j] = -1;
  for (int r = 0; r < GR; r++) for (int c = 0; c < GC; c++) {
    Node *n = &N[r * GC + c]; n->x = R_MAP.x + 60 + c * 132; n->y = R_MAP.y + 76 + r * 146; n->cycle = 24;
    if (r == 0 || r == GR - 1 || c == 0 || c == GC - 1) border[nBorder++] = r * GC + c;
  }
  for (int r = 0; r < GR; r++) for (int c = 0; c < GC - 1; c++) AddRoad(r * GC + c, r * GC + c + 1, 1, r == 1);
  for (int r = 0; r < GR - 1; r++) for (int c = 0; c < GC; c++) AddRoad(r * GC + c, (r + 1) * GC + c, 0, c == 2);
  SetWave(); Route();
  cx3 = (N[0].x + N[GC - 1].x) / 2; cy3 = (N[0].y + N[NN - 1].y) / 2;
  rt3 = LoadRenderTexture(1528, 1028); SetTextureFilter(rt3.texture, TEXTURE_FILTER_BILINEAR);
  for (int r = 0; r < GR - 1; r++) for (int c = 0; c < GC - 1; c++) for (int k = 0; k < 4; k++) {
    float mid = 1 - (fabsf(c - 2.0f) / 2.5f + fabsf(r - 1.0f) / 1.5f) * .4f; bh[r][c][k] = (1.2f + rnd() * 4.2f) * mid; bcol[r][c][k] = GetRandomValue(0, 4);
  }
  for (int i = 0; i < 110; i++) drops3[i] = (Vector3){(rnd() - .5f) * 80, rnd() * 18, (rnd() - .5f) * 60};
  for (int i = 0; i < NDROP; i++) drops[i] = (Vector2){R_MAP.x + rnd() * R_MAP.width, R_MAP.y + rnd() * R_MAP.height};
  for (int s = 0; s < 600; s++) SimStep(.05f); /* warm up so the city starts alive */
  delayH = co2T = 0; kpiT[3] = kpiT[4] = 0;
  memcpy(kpiD, kpiT, sizeof kpiT); memcpy(kpiRef, kpiT, sizeof kpiT);
  AddFeed("System online: 24 junctions monitored", C_GREEN);

  while (!WindowShouldClose()) {
    float dt = fminf(GetFrameTime(), .05f), wh = GetMouseWheelMove(); int hn, he;
    tip.on = 0; introT += dt; toastT = fmaxf(0, toastT - dt);
    if (IsKeyPressed(KEY_P)) paused = !paused;
    if (IsKeyPressed(KEY_ONE)) speedIdx = 0;
    if (IsKeyPressed(KEY_TWO)) speedIdx = 1;
    if (IsKeyPressed(KEY_FOUR)) speedIdx = 2;
    if (IsKeyPressed(KEY_S)) DoStadium();
    if (IsKeyPressed(KEY_R)) DoRain();
    if (IsKeyPressed(KEY_G)) { greenWave = !greenWave; SetWave(); AddFeed(greenWave ? "Green wave enabled" : "Signals back to uncoordinated", C_AMBER); Toast(greenWave ? "Green wave ON" : "Green wave OFF"); }
    hn = he = -1;
    if (!view3d && Hover(R_MAP)) {
      Vector2 m = GetMousePosition();
      for (int i = 0; i < NN; i++) if (Vector2Distance(m, NP(i)) < 13) { hn = i; break; }
      if (hn < 0) for (int e = 0; e < nE; e += 2) if (SegD(m, NP(E[e].a), NP(E[e].b)) < 9) { he = e; break; }
    }
    if (hn >= 0 && wh != 0) N[hn].cycle = Clamp(N[hn].cycle + wh * 2, 10, 60);
    if (IsKeyPressed(KEY_C)) { if (he >= 0) StartCrash(E[he ^ 1].cnt > E[he].cnt ? he ^ 1 : he); else DoCrash(); }
    if (IsKeyPressed(KEY_W)) { if (he >= 0) StartWorks(he); else DoWorks(); }
    if (IsKeyPressed(KEY_X)) ClearIncidents();
    if (IsKeyPressed(KEY_V)) view3d = !view3d;
    if (IsKeyPressed(KEY_F)) {
      view3d = 1;
      if (followCar >= 0) followCar = -1;
      else for (int k = 0; k < 60; k++) { int c = GetRandomValue(0, NCAR - 1); if (cars[c].on) { followCar = c; break; } }
    }
    if (IsMouseButtonPressed(MOUSE_LEFT_BUTTON)) {
      for (int i = 0; i < 4; i++) if (Hover((Rectangle){696 + i * 94, 22, 86, 40})) { if (i == 0) DoCrash(); else if (i == 1) DoStadium(); else if (i == 2) DoRain(); else DoWorks(); }
      for (int i = 0; i < 3; i++) if (Hover((Rectangle){1080 + i * 56, 26, 56, 32})) speedIdx = i;
      { Rectangle t2 = {R_MAP.x + 132, R_MAP.y + 10, 96, 26}; if (Hover(t2)) view3d = GetMouseX() > t2.x + 48; }
      if (he >= 0 && (IsKeyDown(KEY_LEFT_CONTROL) || IsKeyDown(KEY_RIGHT_CONTROL))) StartWorks(he);
      else if (he >= 0 && (IsKeyDown(KEY_LEFT_SHIFT) || IsKeyDown(KEY_RIGHT_SHIFT))) StartCrash(E[he ^ 1].cnt > E[he].cnt ? he ^ 1 : he);
      else if (he >= 0) {
        char a[8], b[8], t[72]; E[he].closed = !E[he].closed; E[he ^ 1].closed = E[he].closed; Route();
        NName(E[he].a, a); NName(E[he].b, b); snprintf(t, 72, "Road %s - %s %s", a, b, E[he].closed ? "closed" : "reopened");
        AddFeed(t, E[he].closed ? C_AMBER : C_GREEN);
      }
    }
    if (view3d) {
      Vector2 md = GetMouseDelta(); float sy = sinf(camYaw), cw = cosf(camYaw), kp = camDist * .0012f;
      if (IsMouseButtonPressed(MOUSE_LEFT_BUTTON) || IsMouseButtonPressed(MOUSE_RIGHT_BUTTON)) drag3d = Hover(R_MAP) && !Hover((Rectangle){R_MAP.x + 132, R_MAP.y + 10, 96, 26});
      if (!IsMouseButtonDown(MOUSE_LEFT_BUTTON) && !IsMouseButtonDown(MOUSE_RIGHT_BUTTON)) drag3d = 0;
      if (drag3d && IsMouseButtonDown(MOUSE_LEFT_BUTTON)) { camYaw -= md.x * .006f; camPitch = Clamp(camPitch + md.y * .006f, .12f, 1.45f); }
      if (drag3d && IsMouseButtonDown(MOUSE_RIGHT_BUTTON)) { camT.x += (-cw * md.x - sy * md.y) * kp; camT.z += (sy * md.x - cw * md.y) * kp; followCar = -1; }
      if (Hover(R_MAP) && wh != 0) { if (followCar >= 0) followDist = Clamp(followDist * (1 - wh * .1f), 6, 60); else userDist = Clamp(userDist * (1 - wh * .1f), 12, 140); }
      UpdateCam3D(dt);
    }
    if (!paused) for (int k = 0; k < MULT[speedIdx]; k++) SimStep(dt);
    for (int i = 0; i < 5; i++) kpiD[i] = Appr(kpiD[i], kpiT[i], 6, dt);

    if (view3d) Render3D();
    BeginDrawing();
    ClearBackground(C_BG);
    Glow(120, 60, 520, C_VIOLET, .16f);
    Glow(SW - 100, SH - 40, 560, C_CYAN, .10f);
    DrawHeader();
    for (int i = 0; i < 5; i++) DrawKpi(i);
    if (view3d) DrawMap3D(); else DrawMap(hn, he);
    DrawViewToggle(); DrawEvents(); DrawHot(); DrawFeed();
    Txt("1 2 4  speed      C  crash      S  stadium      R  rain      W  roadworks      X  clear      G  green wave      P  pause      V  2D/3D      F  follow a car      (hover a road + C or W places it there)", SW / 2, 780, 12, C_MUTED, 0, AC);
    DrawOverlay();
    if (introT < .6f) DrawRectangle(0, 0, SW, SH, Fade(C_BG, 1 - introT / .6f));
    EndDrawing();
  }
  UnloadRenderTexture(rt3);
  CloseWindow();
  return 0;
}