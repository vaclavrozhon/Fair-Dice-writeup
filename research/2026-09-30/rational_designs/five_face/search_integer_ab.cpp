// Exact rational local-model search: a,b share denominator D; c unrestricted.
#include <algorithm>
#include <array>
#include <cmath>
#include <cstdint>
#include <fstream>
#include <iostream>
using I=long long;
I mod(I x,I p){x%=p;return x<0?x+p:x;}
I pw(I a,I e,I p){I r=1;for(;e;e>>=1,a=a*a%p)if(e&1)r=r*a%p;return r;}
bool compat(const std::array<I,5>&a,const std::array<I,5>&b,I D,I p){
 I m[6][6]={};
 for(int j=0;j<5;j++){I A=mod(a[j],p),B=mod(b[j],p);m[0][j]=1;m[1][j]=A;m[2][j]=B;m[3][j]=A*A%p;m[4][j]=A*B%p;m[5][j]=A*A%p*B%p;}
 m[1][5]=m[2][5]=mod(5*D*D/3,p);m[5][5]=pw(D,4,p);
 int rank=0;
 for(int c=0;c<5;c++){
  int r=rank;while(r<6&&m[r][c]==0)r++;
  if(r==6)continue;
  for(int j=c;j<6;j++)std::swap(m[r][j],m[rank][j]);
  I inv=pw(m[rank][c],p-2,p);
  for(int j=c;j<6;j++)m[rank][j]=m[rank][j]*inv%p;
  for(int i=rank+1;i<6;i++){I q=m[i][c];for(int j=c;j<6;j++)m[i][j]=mod(m[i][j]-q*m[rank][j],p);}
  rank++;
 }
 for(int i=rank;i<6;i++)if(m[i][5])return false;
 return true;
}
int main(int argc,char**argv){
 int maxD=argc>1?std::stoi(argv[1]):300;
 std::ofstream out("research/2026-09-30/rational_designs/five_face/integer_ab_candidates.jsonl");
 I na=0,nb=0,nc=0;
 for(I D=3;D<=maxD;D+=3){
  I norm=5*D*D/3;
  for(I a0=std::ceil(-.90*D);a0<=std::floor(-.75*D);a0++)
   for(I a1=std::ceil(-.48*D);a1<=std::floor(-.25*D);a1++)
    for(I a2=std::ceil(-.12*D);a2<=std::floor(.12*D);a2++){
     I S=-a0-a1-a2,T=norm-a0*a0-a1*a1-a2*a2,disc=2*T-S*S;
     if(disc<=0)continue;
     I q=std::llround(std::sqrt((double)disc));if(q*q!=disc||(S-q)%2)continue;
     I a3=(S-q)/2,a4=(S+q)/2;
     if(a3<=a2||a4>=D||a3<.20*D||a3>.55*D||a4<.70*D)continue;
     std::array<I,5>a{a0,a1,a2,a3,a4};na++;
     I da=a1-a0,db=a2-a0,ea=a1*a1-a0*a0,eb=a2*a2-a0*a0,det=da*eb-db*ea;
     for(I b3=-D+3;b3<D;b3++)for(I b4=b3+1;b4<D;b4++){
      I r1=norm+(a0-a3)*b3+(a0-a4)*b4,r2=(a0*a0-a3*a3)*b3+(a0*a0-a4*a4)*b4;
      I n1=r1*eb-r2*db,n2=da*r2-ea*r1;
      if(n1%det||n2%det)continue;
      I b1=n1/det,b2=n2/det,b0=-b1-b2-b3-b4;
      if(b0<=-D||b0>=b1||b1>=b2||b2>=b3)continue;
      std::array<I,5>b{b0,b1,b2,b3,b4};nb++;
      if(!compat(a,b,D,1000003)||!compat(a,b,D,1000033))continue;
      nc++;out<<"{\"D\":"<<D<<",\"a\":[";for(int j=0;j<5;j++)out<<(j?",":"")<<a[j];out<<"],\"b\":[";for(int j=0;j<5;j++)out<<(j?",":"")<<b[j];out<<"]}\n";out.flush();
      std::cout<<"CANDIDATE D "<<D<<" count "<<nc<<std::endl;
     }
    }
  if(D%30==0)std::cout<<"D "<<D<<" a "<<na<<" b "<<nb<<" cand "<<nc<<std::endl;
 }
}
