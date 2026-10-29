enum dupstring {
  STRING_CERT,            /* client certificate filename */
  STRING_CERT_TYPE,       /* format for certificate (default: PEM)*/
  STRING_KEY,             /* private key filename */
  STRING_KEY_PASSWD,      /* plain text private key password */
  STRING_KEY_TYPE,        /* format for private key (default: PEM) */
  STRING_SSL_CAPATH,      /* CA directory name (does not work on Windows) */
  STRING_SSL_CAFILE,      /* certificate file to verify peer against */
  STRING_SSL_PINNEDPUBLICKEY, /* public key file to verify peer against */
  STRING_SSL_CIPHER_LIST, /* list of ciphers to use */
  STRING_SSL_CIPHER13_LIST, /* list of TLS 1.3 ciphers to use */
  STRING_SSL_CRLFILE,     /* crl file to check certificate */
  STRING_SSL_ISSUERCERT, /* issuer cert file to check certificate */
  STRING_SERVICE_NAME,    /* Service name */
#ifndef CURL_DISABLE_PROXY
  STRING_CERT_PROXY,      /* client certificate filename */
  STRING_CERT_TYPE_PROXY, /* format for certificate (default: PEM)*/
  STRING_KEY_PROXY,       /* private key filename */
  STRING_KEY_PASSWD_PROXY, /* plain text private key password */
  STRING_KEY_TYPE_PROXY,  /* format for private key (default: PEM) */
  STRING_SSL_CAPATH_PROXY, /* CA directory name (does not work on Windows) */
  STRING_SSL_CAFILE_PROXY, /* certificate file to verify peer against */
  STRING_SSL_PINNEDPUBLICKEY_PROXY, /* public key file to verify proxy */
  STRING_SSL_CIPHER_LIST_PROXY, /* list of ciphers to use */
  STRING_SSL_CIPHER13_LIST_PROXY, /* list of TLS 1.3 ciphers to use */
  STRING_SSL_CRLFILE_PROXY, /* crl file to check certificate */
  STRING_SSL_ISSUERCERT_PROXY, /* issuer cert file to check certificate */
  STRING_PROXY_SERVICE_NAME, /* Proxy service name */
#endif
#ifndef CURL_DISABLE_COOKIES
  STRING_COOKIE,          /* HTTP cookie string to send */
  STRING_COOKIEJAR,       /* dump all cookies to this file */
#endif
  STRING_CUSTOMREQUEST,   /* HTTP/FTP/RTSP request/method to use */
  STRING_DEFAULT_PROTOCOL, /* Protocol to use when the URL does not specify */
  STRING_DEVICE,          /* local network interface/address to use */
  STRING_INTERFACE,       /* local network interface to use */
  STRING_BINDHOST,        /* local address to use */
  STRING_ENCODING,        /* Accept-Encoding string */
#ifndef CURL_DISABLE_FTP
  STRING_FTP_ACCOUNT,     /* ftp account data */
  STRING_FTP_ALTERNATIVE_TO_USER, /* command to send if USER/PASS fails */
  STRING_FTPPORT,         /* port to send with the FTP PORT command */
#endif
#ifndef CURL_DISABLE_NETRC
  STRING_NETRC_FILE,      /* if not NULL, use this instead of trying to find
                             $HOME/.netrc */
#endif
#ifndef CURL_DISABLE_PROXY
  STRING_PROXY,           /* proxy to use */
  STRING_PRE_PROXY,       /* pre socks proxy to use */
#endif
  STRING_SET_RANGE,       /* range, if used */
  STRING_SET_REFERER,     /* custom string for the HTTP referer field */
  STRING_SET_URL,         /* what original URL to work on */
  STRING_USERAGENT,       /* User-Agent string */
  STRING_SSL_ENGINE,      /* name of ssl engine */
  STRING_USERNAME,        /* <username>, if used */
  STRING_PASSWORD,        /* <password>, if used */
  STRING_OPTIONS,         /* <options>, if used */
#ifndef CURL_DISABLE_PROXY
  STRING_PROXYUSERNAME,   /* Proxy <username>, if used */
  STRING_PROXYPASSWORD,   /* Proxy <password>, if used */
  STRING_NOPROXY,         /* List of hosts which should not use the proxy, if
                             used */
#endif
#ifndef CURL_DISABLE_RTSP
  STRING_RTSP_SESSION_ID, /* Session ID to use */
  STRING_RTSP_STREAM_URI, /* Stream URI for this request */
  STRING_RTSP_TRANSPORT,  /* Transport for this session */
#endif
#ifdef USE_SSH
  STRING_SSH_PRIVATE_KEY, /* path to the private key file for auth */
  STRING_SSH_PUBLIC_KEY,  /* path to the public key file for auth */
  STRING_SSH_HOST_PUBLIC_KEY_MD5, /* md5 of host public key in ASCII hex */
  STRING_SSH_HOST_PUBLIC_KEY_SHA256, /* sha256 of host public key in base64 */
  STRING_SSH_KNOWNHOSTS,  /* filename of knownhosts file */
#endif
#ifndef CURL_DISABLE_SMTP
  STRING_MAIL_FROM,
  STRING_MAIL_AUTH,
#endif
#ifdef USE_TLS_SRP
  STRING_TLSAUTH_USERNAME,  /* TLS auth <username> */
  STRING_TLSAUTH_PASSWORD,  /* TLS auth <password> */
#ifndef CURL_DISABLE_PROXY
  STRING_TLSAUTH_USERNAME_PROXY, /* TLS auth <username> */
  STRING_TLSAUTH_PASSWORD_PROXY, /* TLS auth <password> */
#endif
#endif
  STRING_BEARER,                /* <bearer>, if used */
#ifdef USE_UNIX_SOCKETS
  STRING_UNIX_SOCKET_PATH,      /* path to Unix socket, if used */
#endif
  STRING_TARGET,                /* CURLOPT_REQUEST_TARGET */
#ifndef CURL_DISABLE_DOH
  STRING_DOH,                   /* CURLOPT_DOH_URL */
#endif
#ifndef CURL_DISABLE_ALTSVC
  STRING_ALTSVC,                /* CURLOPT_ALTSVC */
#endif
#ifndef CURL_DISABLE_HSTS
  STRING_HSTS,                  /* CURLOPT_HSTS */
#endif
  STRING_SASL_AUTHZID,          /* CURLOPT_SASL_AUTHZID */
#ifdef USE_ARES
  STRING_DNS_SERVERS,
  STRING_DNS_INTERFACE,
  STRING_DNS_LOCAL_IP4,
  STRING_DNS_LOCAL_IP6,
#endif
  STRING_SSL_EC_CURVES,
#ifndef CURL_DISABLE_AWS
  STRING_AWS_SIGV4, /* Parameters for V4 signature */
#endif
#ifndef CURL_DISABLE_PROXY
  STRING_HAPROXY_CLIENT_IP,     /* CURLOPT_HAPROXY_CLIENT_IP */
#endif
  STRING_ECH_CONFIG,            /* CURLOPT_ECH_CONFIG */
  STRING_ECH_PUBLIC,            /* CURLOPT_ECH_PUBLIC */
  STRING_SSL_SIGNATURE_ALGORITHMS, /* CURLOPT_SSL_SIGNATURE_ALGORITHMS */

  /* -- end of null-terminated strings -- */

  STRING_LASTZEROTERMINATED,

  /* -- below this are pointers to binary data that cannot be strdup'ed. --- */

  STRING_COPYPOSTFIELDS,  /* if POST, set the fields' values here */

  STRING_LAST /* not used, just an end-of-list marker */
};
