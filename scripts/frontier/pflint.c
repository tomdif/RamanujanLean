#include <flint/flint.h>
#include <flint/nmod_poly.h>
#include <stdio.h>
#include <stdlib.h>
int main(int argc,char**argv){
  slong L=atol(argv[1]); ulong M=strtoull(argv[2],0,10); const char*out=argv[3];
  nmod_poly_t E,P; nmod_poly_init(E,M); nmod_poly_init(P,M);
  for(slong k=-100000;k<=100000;k++){ slong e=k*(3*k-1)/2; if(e>=0&&e<L){ ulong c=(k%2==0)?1:M-1; nmod_poly_set_coeff_ui(E,e,c);} }
  nmod_poly_inv_series(P,E,L);
  FILE*f=fopen(out,"wb");
  for(slong i=0;i<L;i++){ ulong c=nmod_poly_get_coeff_ui(P,i); fwrite(&c,8,1,f);} fclose(f);
  return 0;
}
