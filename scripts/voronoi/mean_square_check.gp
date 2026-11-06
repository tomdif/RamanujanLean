default(nbthreads,1);
N=30000; v=vector(N+20,n,ramanujantau(n)*1.0/n^(11/2));
\\ G normalized: sigma^12 * sum tau(n)tau(n+h) e^{-nW}; use lam: tau(n)tau(n+h)=lam lam (n(n+h))^{11/2}
G(h,s,th)={my(W=s*(1+I*th),S=0.);for(n=1,N,S+=v[n]*v[n+h]*(n*(n+h)*1.0)^(11/2)*exp(-n*W));s^12*S};
{for(h=1,2,foreach([0.02,0.005,0.00125],s,print(h," ",s," ",vector(4,j,abs(G(h,s,[0,1,4,16][j]))))))}
\\ h=0 for comparison
{foreach([0.02,0.005,0.00125],s,print("h0 ",s," ",abs(G(0,s,0))))}
quit
