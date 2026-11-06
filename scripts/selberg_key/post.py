"""Post-process sk.c output: test SKQFHyp clauses (i), (ii).
I(L) = int_{-h}^{h} (h-|v|) Re A(v,L) dv = 2 int_0^h (h-v) Re A(v,L) dv   (Re A is even in v),
A(v,L) = r0/(iv) (e^{-v^2/4} S0(v) - e^{-ivL} S(v)) + gR e^{-ivL} S(v).
Real setting: y = T^theta, log T = log y / theta, h = K / log T, L in [log T - log 4pi, log T]."""
import sys, numpy as np
r0, gR = 0.38408405446817037, 0.79602826
def load(y):
    d = np.loadtxt('S_y%d.txt' % y)
    v = d[:, 0]; S = d[:, 1] + 1j * d[:, 2]; S0 = d[:, 3] + 1j * d[:, 4]
    return v, S, S0
def interp(v, F, w):
    return np.interp(w, v, F.real) + 1j * np.interp(w, v, F.imag)
def Ival(v, S, S0, h, L, n=4000):
    w = np.linspace(0, h, n + 1)[1:]
    Sw, S0w = interp(v, S, w), interp(v, S0, w)
    ph = np.exp(-1j * w * L)
    A = r0 / (1j * w) * (np.exp(-w * w / 4) * S0w - ph * Sw) + gR * ph * Sw
    f = (h - w) * A.real
    # v=0 limit by linear extrapolation
    f0 = 2 * f[0] - f[1]
    ff = np.concatenate([[f0], f]); ww = np.concatenate([[0.0], w])
    return 2 * np.trapz(ff, ww)
def I_trivial(h, L, n=4000):  # y = 1: S = S0 = 1
    w = np.linspace(0, h, n + 1)[1:]
    f = (h - w) * (r0 * np.sin(w * L) / w + gR * np.cos(w * L))
    ff = np.concatenate([[h * r0 * L], f]); ww = np.concatenate([[0.0], w])
    return 2 * np.trapz(ff, ww)
if __name__ == '__main__':
    ys = [int(a) for a in sys.argv[1:]] or [30, 60, 100, 200]
    for th in (0.25, 0.1, 0.05):
        print('=== theta = %.3f ===' % th)
        for y in ys:
            v, S, S0 = load(y); ly = np.log(y); logT = ly / th
            print(' y=%d  Q0=S(0)=%.5f  Q0*log y=%.4f' % (y, S[0].real, S[0].real * ly))
            for K in (1, 2, 4, 8, 16, 32, 64):
                h = K / logT
                if h > v[-1]: continue
                Ls = np.linspace(logT - np.log(4 * np.pi), logT, 41)
                I = np.array([Ival(v, S, S0, h, L) for L in Ls])
                It = np.array([I_trivial(h, L) for L in Ls])
                Smax = np.abs(S[v <= h]).max()
                print('  K=%3d h=%.4f  max|S|=%.4f  max_L|I|/h^2=%.4f  mean_L I/h^2=%.4f  sqrtK*max=%.4f'
                      '   [y=1: mean I/h^2=%.2f]' % (K, h, Smax, np.abs(I).max() / h**2, I.mean() / h**2,
                                                   np.sqrt(K) * np.abs(I).max() / h**2, It.mean() / h**2))
