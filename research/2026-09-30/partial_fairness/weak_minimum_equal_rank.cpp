#include <algorithm>
#include <cmath>
#include <iostream>
#include <numeric>
#include <vector>
using namespace std;
// Exact necessary Gram identity at q=n-1=3h, plus determinant squareness.
int h,q; long long L, target, identities,squares;
vector<int> c;
bool square_rational(long long A){
  long long z=h;
  vector<int> primes;
  for(int p=2;p<=max<long long>(A,h);p++){
    bool prime=true; for(int d=2;d*d<=p;d++)if(p%d==0){prime=false;break;}
    if(!prime)continue;
    int parity=0;
    auto val=[&](long long n){int a=0;while(n%p==0){n/=p;a++;}return a;};
    parity=val(h)-val(A);
    for(int e=1;e<=h;e++)parity+=c[e]*val(e);
    if(parity%2)return false;
  }
  return true;
}
void rec(int e,int left,long long S,long long U){
  if(e==h){
    c[e]=left;S+=1LL*e*left;U+=L/e*left;
    long long A=S-2*h, B=L+h*U;
    if(A*B!=target)return;
    identities++;
    if(square_rational(A)){
      squares++;
      if(squares<=12){cout<<"h="<<h<<" profile";for(int i=1;i<=h;i++)cout<<' '<<c[i];cout<<" A="<<A<<" B/L="<<B<<'/'<<L<<'\n';}
    }
    return;
  }
  for(int a=0;a<=left;a++){c[e]=a;rec(e+1,left-a,S+1LL*a*e,U+a*(L/e));}
}
int main(int argc,char**argv){
  int maxh=argc>1?stoi(argv[1]):9;
  for(h=1;h<=maxh;h++){
    q=3*h;L=1;for(int e=1;e<=h;e++)L=lcm(L,(long long)e);
    target=1LL*h*(q-1)*(q-1)*L;c.assign(h+1,0);identities=squares=0;
    rec(1,q,0,0);
    cout<<"SUMMARY h="<<h<<" identity="<<identities<<" square="<<squares<<endl;
  }
}
