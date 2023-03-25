'''
Python 2.7 implementation of
PKCS #1 v2.1: RSA Cryptography Standard (June 14, 2002)
Written by Brent Zundel
'''
from modmath import *

def RSAkeys(b, num = 2):
  '''
  RSAkeys(b, [num = 2]) -> (pub, pri)

  RSAkeys generates public and private keys for RSA cryptosystems,
  suitable for encrypting byte streams of length b.
  pub is a tuple (n, e), where n is the RSA modulus and e is the public exponent
  For num == 2, pri is a tuple (n, d), where
      n is the RSA modulus and d is the private exponent.
  For num > 2, pri is a tuple (quint, tripList), where
      quint is a quintuple (p, q, dP, dQ, qInv), with
          p = the first prime factor of n
          q = the second prime factor of n
          dP = the first factor's CRT exponent
          dQ = the second factor's CRT exponent
          qInv = the first CRT coefficient
        and tripList is a list of tuples (ri, di, ti), with
          ri = the ith factor
          di = the ith factor's CRT exponent
          ti = the ith factor's CRT coefficient
  '''
  from operator import mul
  B = b * 8
  factSize = B / num - 1
  r = set()
  x = num
  while True:
    for i in range(x):
      r.add(findPrime(factSize))
    lr = len(r)
    if lr == num:
      break
    else:
      x = num - lr
  r = list(r)
  n = reduce(mul, r)
  lam = lcmList(map(lambda x: x-1, r))
  e = 65537
  while not relPrime(lam, e):
    e += 2
  if num == 2:
    d = invMod(e,lam)
    return ((n,e),(n,d))
  elif num > 2:
    dP = invMod(e,r[0]-1)
    dQ = invMod(e, r[1]-1)
    qInv = invMod(r[1],r[0])
    if qInv > r[0]:
      raise Exception("qInv > p")
    trip = []
    R = r[0]*r[1]
    for ri in r[2:]:
      di = invMod(e, ri - 1)
      ti = invMod(R, ri)
      R *= ri
      trip.append((ri, di, ti))
    return ((n, e), ((r[0],r[1],dP,dQ,qInv),trip))
  else: raise Exception("Number of prime factors must be > 1")


def OS2IP(byteString):
  '''
  OS2IP(byteString) -> long integer

  OS2IP converts a string of bytes (an Octet String)
  to a long integer. It is defined in the
  PKCS #1 v2.1: RSA Cryptography Standard (June 14, 2002)
  '''
  from binascii import hexlify
  return long(hexlify(byteString),16)


def I2OSP(longint, length):
  '''
  I2OSP(longint, length) -> bytes

  I2OSP converts a long integer into a string of
  bytes (an Octet String). It is defined in the
  PKCS #1 v2.1: RSA Cryptography Standard (June 14, 2002)
  '''
  from binascii import unhexlify
  if type(longint) == type(int()):
    return I2OSP(long(longint), length)
  if type(longint) != type(long()):
    raise Exception("first argument must be a long or an int")
  b1 = bytes()
  b2 = bytes()
  x = longint
  size = (longint.bit_length()+7) / 8 
  if size > length:
    raise Exception ("integer too large for length")
  while length > size:
    b1 += '\x00'
    length -= 1
  hx = hex(longint)[2:-1]
  if len(hx) % 2 == 1:
    hx = '0' + hx
  if longint == 0:
    b2 = ''
  else:
    b2 = unhexlify(hx)
  return b1 + b2


def RSAEP(pub, m):
  '''
  RSAEP(pub, m) -> long integer

  RSAEP performs an encryption operation on a long integer.
  It is an encryption primitive defined in the
  PKCS #1 v2.1: RSA Cryptography Standard (June 14, 2002).

  pub is an RSA public key consisting of a tuple (n, e), where
    n = the RSA modulus,
    e = the public exponent,
  and m is a positive integer representation of a byte string.
  m must be less than n.
  '''
  if m > (pub[0] - 1) or m < 0:
    raise Exception("message representative out of range")
  else:
    return modExp(m, pub[1], pub[0])


def RSADP(pri, c):
  '''
  RSADP(pri, c) -> long integer

  RSADP performs a decryption operation on a long integer.
  It is a decryption primitive defined in the
  PKCS #1 v2.1: RSA Cryptography Standard (June 14, 2002).
  
  pri is an RSA private key, represented by
    a tuple (n, d), where
      n = the RSA modulus,
      d = the private exponent,
    or by a tuple (quint, tripList), where
      quint is a quintuple (p, q, dP, dQ, qInv), with
        p = the first prime factor of n,
        q = the second prime factor of n,
        dP = the first factor's CRT exponent,
        dQ = the second factor's CRT exponent,
        qInv = the first CRT coefficient,
      and tripList is a list of tuples (ri, di, ti), with
        ri = the ith factor,
        di = the ith factor's CRT exponent,
        ti = the ith factor's CRT coefficient.
  The size of c that can be decrypted is limited by:
    n in the first representation, or
    min(p, q, r1, r2, . . ., rn) in the second representation.
  '''
  if type(pri[0]) == tuple:
    quint = pri[0]
    mi = []
    if c > quint[0]  - 1 or c < 0:
      raise Exception("ciphertext representative out of range")
    mi.append(modExp(c, quint[2], quint[0]))
    if c > quint[1]  - 1:
      raise Exception("ciphertext representative out of range")
    mi.append(modExp(c, quint[3], quint[1]))
    for trip in pri[1]:
      if c > trip[0] - 1:
        raise Exception("ciphertext representative out of range")
      mi.append(modExp(c, trip[1], trip[0]))
    h = (mi[0] - mi[1]) * (quint[4] % quint[0])
    m = mi[1] + quint[1] * h
    R = quint[0] * quint[1]
    i = 2
    for trip in pri[1]:
      h = ((mi[i] - m) * trip[2]) % trip[0]
      m = m + R * h
      R *= trip[0]
    return m
  else:
    if c > pri[0] - 1 or c < 0:
      raise Exception("ciphertext representative out of range")
    return modExp(c, pri[1], pri[0])


def RSASP1(pri, m):
  '''
  RSADP(pri, m) -> long integer

  RSADP performs a digital signature operation on a long integer.
  It is a signature primitive defined in the
  PKCS #1 v2.1: RSA Cryptography Standard (June 14, 2002).
  
  pri is an RSA private key, represented by
    a tuple (n, d), where
      n = the RSA modulus,
      d = the private exponent,
    or by a tuple (quint, tripList), where
      quint is a quintuple (p, q, dP, dQ, qInv), with
        p = the first prime factor of n,
        q = the second prime factor of n,
        dP = the first factor's CRT exponent,
        dQ = the second factor's CRT exponent,
        qInv = the first CRT coefficient,
      and tripList is a list of tuples (ri, di, ti), with
        ri = the ith factor,
        di = the ith factor's CRT exponent,
        ti = the ith factor's CRT coefficient.
  m is a long integer representative of a byte string.
  The size of m that can be signed is limited by:
    n in the first pri representation, or
    p in the second pri representation.
  '''
  if type(pri[0]) == tuple:
    quint = pri[0]
    si = []
    if m > quint[0]  - 1 or m < 0:
      raise Exception("message representative out of range")
    si.append(modExp(m, quint[2], quint[0]))
    if m > quint[1]  -1:
      raise Exception("message representative out of range")
    si.append(modExp(m, quint[3], quint[1]))
    for trip in pri[1]:
      if m > trip[0]  - 1:
        raise Exception("message representative out of range")
      si.append(modExp(m, trip[1], trip[0]))
    h = (si[0] - si[1]) * (quint[4] % quint[0])
    s = si[1] + quint[1] * h
    R = quint[0] * quint[1]
    i = 2
    for trip in pri[1]:
      h = ((si[i] - s) * trip[2]) % trip[0]
      s = s + R * h
      R *= trip[0]
    return s
  else:
    if m > pri[0] - 1 or c < 0:
      raise Exception("message representative out of range")
    return modExp(m, pri[1], pri[0])


def RSAVP1(pub, s):
  '''
  RSAEP(pub, s) -> long

  RSAEP performs a digital signature verification of a long integer.
  It is a signature primitive defined in the
  PKCS #1 v2.1: RSA Cryptography Standard (June 14, 2002).
  
  pub is an RSA public key consisting of a tuple (n, e), where
    n = the modulus,
    e = the public exponent,
  and s is a positive integer representative of a signature.
  s must be less than n.
  '''
  if s > (pub[0] - 1) or s < 0:
    raise Exception("signature representative out of range")
  else:
    return modExp(s, pub[1], pub[0])


def MGF1(mgfSeed, maskLen):
  '''
  MGF1(mgfSeed, maskLen) -> bytes

  MGF1 uses mgfSeed to generate a mask of maskLen bytes.
  It is defined in the PKCS #1 v2.1: RSA Cryptography Standard (June 14, 2002)
  '''
  from hashlib import sha1
  sh = sha1()
  hLen = sh.digest_size
  if maskLen > (hLen << 32):
    raise Exception('mask too long')
  T = bytes()
  counter = 0
  while len(T) < maskLen:
    C = I2OSP(counter, 4)
    sh.update(mgfSeed + C)
    T = T + sh.digest()
    counter += 1
  return T[0:maskLen]


def emptyBytes(n):
  '''
  emptyBytes(n) -> bytes

  emptyBytes returns a byte string of zeros, n bytes long
  '''
  es = bytes()
  while n > 0:
    es += '\x00'
    n -= 1
  return es

def xor(byteString1, byteString2):
  '''
  xor(byteString1, byteString2) -> bytes

  xor performs the exclusive-or operation on two byte strings.
  '''
  length = len(byteString1)
  if length != len(byteString2):
    raise Exception("Byte strings are of different lengths")
  bs1 = OS2IP(byteString1)
  bs2 = OS2IP(byteString2)
  return I2OSP(bs1 ^ bs2, length)


def modLen(key):
  '''
  modLen(key) -> number

  modLen takes either a public or private key and returns a number
  indicating the maximum number of bytes that can be encrypted or
  decrypted using the key.
  The public key consists of a tuple (n, e) where
    n = the modulus
    e = the public exponent
  the private key consists of either
    a tuple (n, d), where
      n = the RSA modulus,
      d = the private exponent,
    or by a tuple (quint, tripList), where
      quint is a quintuple (p, q, dP, dQ, qInv), with
        p = the first prime factor of n,
        q = the second prime factor of n,
        dP = the first factor's CRT exponent,
        dQ = the second factor's CRT exponent,
        qInv = the first CRT coefficient,
      and tripList is a list of tuples (ri, di, ti), with
        ri = the ith factor,
        di = the ith factor's CRT exponent,
        ti = the ith factor's CRT coefficient.
  '''
  if type(pri[0]) == tuple:
    quint = pri[0]
    li = [quint[0].bit_length(), quint[1].bit_length()]
    for trip in pri[1]:
      li.append(trip[0].bit_length)
    length = min(li)
  else:
    length = pri[0].bit_length()
  return (length + 7) // 8


def RSAES_OAEP_Encrypt(pub, M, L=''):
  '''
  RSAES_OAEP_Encrypt(pub, M, L='') -> Bytes

  RSAES_OAEP_Encrypt is the encryption operation described
  in the PKCS #1 v2.1: RSA Cryptography Standard (June 14, 2002).
  
  pub is a public key consisting of a tuple (n, e) where
    n = the RSA modulus
    e = the public exponent
  M is the message to be encrypted, a byte string
  L is an optional label to be associated with the message
  '''
  if len(L) > ((1 << 61) - 1):
    raise Exception("Label too long")
  from hashlib import sha1
  from os import urandom
  sh = sha1()
  mLen = len(M)
  hLen = sh.digest_size
  k = modLen(pub)
  maxLen = (k-2*hLen-2)
  sh.update(L)
  lHash = sh.digest()
  if mLen > maxLen:
    raise Exception("Message too long")
  PS = emptyBytes(k - mLen - 2*hLen - 2)
  DB = lHash + PS + '\x01' + M
  if len(DB) != (k - hLen - 1):
    raise Exception("DB is length %d, should be length %d" %(len(DB), (k - hLen - 1)))
  seed = urandom(hLen)
  dbMask = MGF1(seed, k - hLen - 1)
  maskedDB = xor(DB, dbMask)
  seedMask = MGF1(maskedDB, hLen)
  maskedSeed = xor(seed, seedMask)
  EM = '\x00' + maskedSeed + maskedDB
  m = OS2IP(EM)
  c = RSAEP(pub, m)
  return I2OSP(c, k)


def sepDB(DB, hLen):
  '''
  sepDB(DB) -> (lHashP, PS, one, M)

  sepDB is a helper function for RSAES_OAEP_Decrypt.
  It separates DB into its component parts.
  '''
  i = 0
  for x in DB[hLen:]:
    if x == '\x00':
      i += 1
    elif x == '\x01':
      break
    else:
      raise Exception("DB Error")
  return (DB[0:hLen], DB[hLen:hLen+i], DB[hLen+i], DB[hLen+i+1:])


def RSAES_OAEP_Decrypt(pri, C, L=''):
  '''
  RSAES_OAEP_Decrypt(pri, C, L='') -> bytes

  RSAES_OAEP_Decrypt is the decryption operation described
  in the PKCS #1 v2.1: RSA Cryptography Standard (June 14, 2002).
  
  pri is a private key consisting of a tuple (n, d) where
    n = the modulus, k bytes long
    d = the private exponent
  C is the ciphertext to be decrypted, a byte string.
    It cannot be longer than k bytes.
  L is an optional label whose association with the message is to be verified
  '''
  if len(L) > ((1 << 61) - 1):
    raise Exception("Decryption Error")
  from hashlib import sha1
  from os import urandom
  sh = sha1()
  cLen = len(C)
  hLen = sh.digest_size
  k = modLen(pri)
  if k < (2*hLen +2):
    raise Exception("Decryption Error")
  if cLen != k:
    raise Exception("Decryption Error")
  c = OS2IP(C)
  try:
    m = RSADP(pri, c)
  except:
    raise Exception("Decryption Error")
  EM = I2OSP(m, k)
  lHash = sha1(L)
  Y = EM[0]
  maskedSeed = EM[1:hLen+1]
  maskedDB = EM[hLen+1:]
  if len(maskedDB) != (k-hLen-1):
    raise Exception("Decryption Error")
  seedMask = MGF1(maskedDB, hLen)
  seed = xor(maskedSeed, seedMask)
  dbMask = MGF1(seed, k-hLen-1)
  DB = xor(maskedDB, dbMask)
  try:
    (lHashP, PS, one, M) = sepDB(DB, hLen)
  except:
    raise Exception("Decryption Error")
  if one != '\x01':
    raise Exception("Decryption Error")
  if lHash.digest() != lHashP:
    raise Exception("Decryption Error")
  if Y != '\x00':
    raise Exception("Decryption Error")
  return M




def byteSize(OS, size):
  '''
  byteSize(OS, size) -> byte string list

  byteSize returns a byte string OS as a
  list of byte strings of length size.
  '''
  out = []
  i = 0
  OSLen = len(OS)
  while i < OSLen:
    out += [OS[i:i+size]]
    i += size
  return out


def stringEncrypt(pub, M, L=''):
  '''
  stringEncrypt(pub, M, L='') -> Bytes

  stringEncrypt is based on the RSAES_OAEP_Encrypt operation described
  in the PKCS #1 v2.1: RSA Cryptography Standard (June 14, 2002).
  It can be used with strings of arbitrary length.
  
  pub is a public key consisting of a tuple (n, e) where
    n = the modulus
    e = the public exponent
  M is the message to be encrypted, a byte string
  L is an optional label to be associated with the message
  '''
  if len(L) > ((1 << 61) - 1):
    raise Exception("Label too long")
  from hashlib import sha1
  from os import urandom
  sh = sha1()
  mLen = len(M)
  hLen = sh.digest_size
  k = modLen(pub)
  maxLen = (k-2*hLen-2)
  sh.update(L)
  lHash = sh.digest()
  byteList = byteSize(M, maxLen)
  out = bytes()
  for OS in byteList:
    mLen = len(OS)
    PS = emptyBytes(k - mLen - 2*hLen - 2)
    DB = lHash + PS + '\x01' + OS
    if len(DB) != (k - hLen - 1):
      raise Exception("DB is length %d, should be length %d" %(len(DB), (k - hLen - 1)))
    seed = urandom(hLen)
    dbMask = MGF1(seed, k - hLen - 1)
    maskedDB = xor(DB, dbMask)
    seedMask = MGF1(maskedDB, hLen)
    maskedSeed = xor(seed, seedMask)
    EM = '\x00' + maskedSeed + maskedDB
    m = OS2IP(EM)
    c = RSAEP(pub, m)
    out += I2OSP(c, k)
  return out

def stringDecrypt(pri, C, L=''):
  '''
  stringDecrypt(pri, C, L='') -> bytes

  stringDecrypt is based on the RSAES_OAEP_Decrypt operation described
  in the PKCS #1 v2.1: RSA Cryptography Standard (June 14, 2002).
  It can decrypt ciphertexts of arbitrary length.
  
  pri is a private key consisting of a tuple (n, d) where
    n = the modulus
    d = the private exponent
  C is the ciphertext to be decrypted, a byte string
  L is an optional label whose association with the message is to be verified
  '''
  if len(L) > ((1 << 61) - 1):
    raise Exception("Decryption Error")
  from hashlib import sha1
  from os import urandom
  sh = sha1()
  cLen = len(C)
  hLen = sh.digest_size
  k = modLen(pri)
  if k < (2*hLen +2):
    raise Exception("Decryption Error")
  byteList = byteSize(C, k)
  out = bytes()
  for OS in byteList:
    c = OS2IP(OS)
    try:
      m = RSADP(pri, c)
    except:
      raise Exception("Decryption Error")
    EM = I2OSP(m, k)
    lHash = sha1(L)
    Y = EM[0]
    maskedSeed = EM[1:hLen+1]
    maskedDB = EM[hLen+1:]
    if len(maskedDB) != (k-hLen-1):
      raise Exception("Decryption Error")
    seedMask = MGF1(maskedDB, hLen)
    seed = xor(maskedSeed, seedMask)
    dbMask = MGF1(seed, k-hLen-1)
    DB = xor(maskedDB, dbMask)
    try:
      (lHashP, PS, one, M) = sepDB(DB, hLen)
    except:
      raise Exception("Decryption Error")
    if one != '\x01':
      raise Exception("Decryption Error")
    if lHash.digest() != lHashP:
      raise Exception("Decryption Error")
    if Y != '\x00':
      raise Exception("Decryption Error")
    out += M
  return out


def fileEncrypt(pub, inName, outName='myfile', L=''):
  '''
  fileEncrypt(pub, inName, outName='myfile', L='') -> file
  
  fileEncrypt is based on the RSAES_OAEP_Encrypt operation described
  in the PKCS #1 v2.1: RSA Cryptography Standard (June 14, 2002).
  It can encrypt any size file, but files larger
  than 500 kb may take a long time to decrypt.
  
  pub is a public key consisting of a tuple (n, e) where
    n = the modulus
    e = the public exponent
  inName is the name of the input file
  outName is an optional output file name
  L is an optional label to be associated with the message
  '''
  if len(L) > ((1 << 61) - 1):
    raise Exception("Label too long")
  from hashlib import sha1
  from os import urandom
  try:
    fin = file(inName, 'rb')
  except:
    raise Exception("Error opening file: %s" %(inName))
  sh = sha1(L)
  hLen = sh.digest_size
  lHash = sh.digest()
  k = modLen(pub)
  maxLen = (k-2*hLen-2)
  try:
    fout = file(outName, 'wb')
  except:
    raise Exception("Error opening output file")
  OS = fin.read(maxLen)
  while OS != '':
    mLen = len(OS)
    PS = emptyBytes(k - mLen - 2*hLen - 2)
    DB = lHash + PS + '\x01' + OS
    if len(DB) != (k - hLen - 1):
      raise Exception("DB is length %d, should be length %d" %(len(DB), (k - hLen - 1)))
    seed = urandom(hLen)
    dbMask = MGF1(seed, k - hLen - 1)
    maskedDB = xor(DB, dbMask)
    seedMask = MGF1(maskedDB, hLen)
    maskedSeed = xor(seed, seedMask)
    EM = '\x00' + maskedSeed + maskedDB
    m = OS2IP(EM)
    c = RSAEP(pub, m)
    fout.write(I2OSP(c, k))
    OS = fin.read(maxLen)
  fin.close()
  fout.close()


def fileDecrypt(pri, inName, outName='newFile', L=''):
  '''
  fileDecrypt(pri, inName, outName='newFile', L='') -> file

  fileDecrypt is based on the RSAES_OAEP_Decrypt operation described
  in the PKCS #1 v2.1: RSA Cryptography Standard (June 14, 2002).
  It can be used to decrypt any size file, but files
  larger than 500 kb may take a long time to decrypt.
  
  pri is a private key consisting of a tuple (n, d) where
    n = the modulus
    d = the private exponent
  inName is the name of the encrypted file
  outName is an optional output file name
  L is an optional label whose association with the message is to be verified
  '''
  if len(L) > ((1 << 61) - 1):
    raise Exception("Decryption Error")
  from hashlib import sha1
  from os import urandom
  sh = sha1()
  hLen = sh.digest_size
  k = modLen(pri)
  if k < (2*hLen +2):
    raise Exception("Decryption Error")
  fin = file(inName, 'rb')
  fout = file(outName, 'wb')
  OS = fin.read(k)
  while OS != '':
    c = OS2IP(OS)
    try:
      m = RSADP(pri, c)
    except:
      raise Exception("Decryption Error")
    EM = I2OSP(m, k)
    lHash = sha1(L)
    Y = EM[0]
    maskedSeed = EM[1:hLen+1]
    maskedDB = EM[hLen+1:]
    if len(maskedDB) != (k-hLen-1):
      raise Exception("Decryption Error")
    seedMask = MGF1(maskedDB, hLen)
    seed = xor(maskedSeed, seedMask)
    dbMask = MGF1(seed, k-hLen-1)
    DB = xor(maskedDB, dbMask)
    try:
      (lHashP, PS, one, M) = sepDB(DB, hLen)
    except:
      raise Exception("Decryption Error")
    if one != '\x01':
      raise Exception("Decryption Error")
    if lHash.digest() != lHashP:
      raise Exception("Decryption Error")
    if Y != '\x00':
      raise Exception("Decryption Error")
    fout.write(M)
    OS = fin.read(k)
  fin.close()
  fout.close()
