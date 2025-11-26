const os = require('os');
const http = require('http');
const fs = require('fs');
const axios = require('axios');
const net = require('net');
const path = require('path');
const crypto = require('crypto');
const { Buffer } = require('buffer');
const { exec, execSync } = require('child_process');
const { WebSocket, createWebSocketStream } = require('ws');

// 环境变量配置
const UUID = process.env.UUID || '5efabea4-f6d4-91fd-b8f0-17e004c89c60';
const NEZHA_SERVER = process.env.NEZHA_SERVER || '';       
const NEZHA_PORT = process.env.NEZHA_PORT || '';           
const NEZHA_KEY = process.env.NEZHA_KEY || '';             
const DOMAIN = process.env.DOMAIN || 'example.com';       
const AUTO_ACCESS = process.env.AUTO_ACCESS || false;      
const WSPATH = process.env.WSPATH || UUID.slice(0, 8);     
const SUB_PATH = process.env.SUB_PATH || 'sub';            
const NAME = process.env.NAME || '';                       
// Hugging Face 强制要求 7860，这里做个兼容
const PORT = process.env.PORT || 7860;                     

// 获取 ISP 信息
let ISP = '';
const GetISP = async () => {
  try {
    const res = await axios.get('https://speed.cloudflare.com/meta');
    const data = res.data;
    ISP = `${data.country}-${data.asOrganization}`.replace(/ /g, '_');
  } catch (e) {
    ISP = 'Unknown';
  }
}
GetISP();

// ============================================
// HTTP 服务：负责 1.伪装主页 2.订阅输出
// ============================================
const httpServer = http.createServer((req, res) => {
  if (req.url === '/') {
    // 伪装主页逻辑
    const filePath = path.join(__dirname, 'index.html');
    fs.readFile(filePath, 'utf8', (err, content) => {
      if (err) {
        res.writeHead(200, { 'Content-Type': 'text/html' });
        res.end('<h1>Hello World</h1>'); // 找不到index.html时的兜底
        return;
      }
      res.writeHead(200, { 'Content-Type': 'text/html' });
      res.end(content);
    });
    return;
  } else if (req.url === `/${SUB_PATH}`) {
    // 订阅逻辑
    const namePart = NAME ? `${NAME}-${ISP}` : ISP;
    const vlessURL = `vless://${UUID}@cdns.doon.eu.org:443?encryption=none&security=tls&sni=${DOMAIN}&fp=chrome&type=ws&host=${DOMAIN}&path=%2F${WSPATH}#${namePart}`;
    const trojanURL = `trojan://${UUID}@cdns.doon.eu.org:443?security=tls&sni=${DOMAIN}&fp=chrome&type=ws&host=${DOMAIN}&path=%2F${WSPATH}#${namePart}`;
    const subscription = vlessURL + '\n' + trojanURL;
    const base64Content = Buffer.from(subscription).toString('base64');
    
    res.writeHead(200, { 'Content-Type': 'text/plain' });
    res.end(base64Content + '\n');
  } else {
    res.writeHead(404, { 'Content-Type': 'text/plain' });
    res.end('Not Found\n');
  }
});

const wss = new WebSocket.Server({ server: httpServer });
const uuid = UUID.replace(/-/g, "");
const DNS_SERVERS = ['8.8.4.4', '1.1.1.1'];

// DNS 解析逻辑
function resolveHost(host) {
  return new Promise((resolve, reject) => {
    if (/^(?:(?:25[0-5]|2[0-4][0-9]|[01]?[0-9][0-9]?)\.){3}(?:25[0-5]|2[0-4][0-9]|[01]?[0-9][0-9]?)$/.test(host)) {
      resolve(host);
      return;
    }
    let attempts = 0;
    function tryNextDNS() {
      if (attempts >= DNS_SERVERS.length) {
        reject(new Error(`Failed to resolve ${host} with all DNS servers`));
        return;
      }
      const dnsServer = DNS_SERVERS[attempts];
      attempts++;
      const dnsQuery = `https://dns.google/resolve?name=${encodeURIComponent(host)}&type=A`;
      axios.get(dnsQuery, {
        timeout: 5000,
        headers: { 'Accept': 'application/dns-json' }
      })
      .then(response => {
        const data = response.data;
        if (data.Status === 0 && data.Answer && data.Answer.length > 0) {
          const ip = data.Answer.find(record => record.type === 1);
          if (ip) {
            resolve(ip.data);
            return;
          }
        }
        tryNextDNS();
      })
      .catch(error => {
        tryNextDNS();
      });
    }
    tryNextDNS();
  });
}

// ============================================
// 关键修复：VLESS 处理逻辑 (增加 Try-Catch 和长度检查)
// ============================================
function handleVlessConnection(ws, msg) {
  try {
    // 1. 基础长度检查
    if (msg.length < 24) return false; 

    const [VERSION] = msg;
    const id = msg.slice(1, 17);
    if (!id.every((v, i) => v == parseInt(uuid.substr(i * 2, 2), 16))) return false;
    
    // 读取 optLength
    const optLength = msg.slice(17, 18).readUInt8();
    let i = optLength + 19;

    // 2. 动态长度检查：确保后续读取不会越界
    // 需要读 Port(2) + ATYP(1) = 3 字节
    if (msg.length < i + 3) return false;

    const port = msg.slice(i, i + 2).readUInt16BE(0);
    i += 2;
    const ATYP = msg.slice(i, i + 1).readUInt8();
    i += 1;

    let host = '';
    // 根据 ATYP 解析 Host，每一步都检查长度
    if (ATYP == 1) { // IPv4
      if (msg.length < i + 4) return false;
      host = msg.slice(i, i + 4).join('.');
      i += 4;
    } else if (ATYP == 2) { // Domain
      if (msg.length < i + 1) return false;
      const domainLen = msg.slice(i, i + 1).readUInt8();
      i += 1;
      if (msg.length < i + domainLen) return false;
      host = new TextDecoder().decode(msg.slice(i, i + domainLen));
      i += domainLen;
    } else if (ATYP == 3) { // IPv6
      if (msg.length < i + 16) return false;
      host = msg.slice(i, i + 16).reduce((s, b, i, a) => (i % 2 ? s.concat(a.slice(i - 1, i + 1)) : s), []).map(b => b.readUInt16BE(0).toString(16)).join(':');
      i += 16;
    } else {
      return false;
    }

    ws.send(new Uint8Array([VERSION, 0]));
    const duplex = createWebSocketStream(ws);
    
    resolveHost(host)
      .then(resolvedIP => {
        const client = net.connect({ host: resolvedIP, port }, function() {
          this.write(msg.slice(i));
          duplex.on('error', () => {}).pipe(this).on('error', () => {}).pipe(duplex);
        });
        client.on('error', () => {});
      })
      .catch(error => {
        // DNS解析失败，尝试直接连接
        const client = net.connect({ host, port }, function() {
          this.write(msg.slice(i));
          duplex.on('error', () => {}).pipe(this).on('error', () => {}).pipe(duplex);
        });
        client.on('error', () => {});
      });
    
    return true;
  } catch (error) {
    // 捕获所有解析异常，防止进程崩溃
    return false;
  }
}

// Trojan 处理逻辑 (同样增加 Try-Catch)
function handleTrojanConnection(ws, msg) {
  try {
    if (msg.length < 58) return false;
    const receivedPasswordHash = msg.slice(0, 56).toString();
    const possiblePasswords = [UUID];
    
    let matchedPassword = null;
    for (const pwd of possiblePasswords) {
      const hash = crypto.createHash('sha224').update(pwd).digest('hex');
      if (hash === receivedPasswordHash) {
        matchedPassword = pwd;
        break;
      }
    }
    
    if (!matchedPassword) return false;
    let offset = 56;
    if (msg[offset] === 0x0d && msg[offset + 1] === 0x0a) {
      offset += 2;
    }
    
    const cmd = msg[offset];
    if (cmd !== 0x01) return false;
    offset += 1;
    const atyp = msg[offset];
    offset += 1;
    let host, port;
    if (atyp === 0x01) {
      host = msg.slice(offset, offset + 4).join('.');
      offset += 4;
    } else if (atyp === 0x03) {
      const hostLen = msg[offset];
      offset += 1;
      host = msg.slice(offset, offset + hostLen).toString();
      offset += hostLen;
    } else if (atyp === 0x04) {
      host = msg.slice(offset, offset + 16).reduce((s, b, i, a) => 
        (i % 2 ? s.concat(a.slice(i - 1, i + 1)) : s), [])
        .map(b => b.readUInt16BE(0).toString(16)).join(':');
      offset += 16;
    } else {
      return false;
    }
    
    port = msg.readUInt16BE(offset);
    offset += 2;
    
    if (offset < msg.length && msg[offset] === 0x0d && msg[offset + 1] === 0x0a) {
      offset += 2;
    }
    
    const duplex = createWebSocketStream(ws);

    resolveHost(host)
      .then(resolvedIP => {
        const client = net.connect({ host: resolvedIP, port }, function() {
          if (offset < msg.length) {
            this.write(msg.slice(offset));
          }
          duplex.on('error', () => {}).pipe(this).on('error', () => {}).pipe(duplex);
        });
        client.on('error', () => {});
      })
      .catch(error => {
        const client = net.connect({ host, port }, function() {
          if (offset < msg.length) {
            this.write(msg.slice(offset));
          }
          duplex.on('error', () => {}).pipe(this).on('error', () => {}).pipe(duplex);
        });
        client.on('error', () => {});
      });
    
    return true;
  } catch (error) {
    return false;
  }
}

// WS 连接分流
wss.on('connection', (ws, req) => {
  ws.once('message', msg => {
    // 增加数据包长度判断，防止超短包
    if (msg.length > 17 && msg[0] === 0) {
      const id = msg.slice(1, 17);
      const isVless = id.every((v, i) => v == parseInt(uuid.substr(i * 2, 2), 16));
      if (isVless) {
        if (!handleVlessConnection(ws, msg)) {
          ws.close(); // 解析失败安全关闭
        }
        return;
      }
    }
    
    // 如果不是VLESS，尝试Trojan
    if (!handleTrojanConnection(ws, msg)) {
      ws.close();
    }
  }).on('error', () => {});
});

// ============================================
// 哪吒探针下载与运行逻辑 (保持原样)
// ============================================
const getDownloadUrl = () => {
  const arch = os.arch(); 
  if (arch === 'arm' || arch === 'arm64' || arch === 'aarch64') {
    if (!NEZHA_PORT) {
      return 'https://arm64.ssss.nyc.mn/v1';
    } else {
      return 'https://arm64.ssss.nyc.mn/agent';
    }
  } else {
    if (!NEZHA_PORT) {
      return 'https://amd64.ssss.nyc.mn/v1';
    } else {
      return 'https://amd64.ssss.nyc.mn/agent';
    }
  }
};

const downloadFile = async () => {
  if (!NEZHA_SERVER && !NEZHA_KEY) return;
  
  try {
    const url = getDownloadUrl();
    const response = await axios({
      method: 'get',
      url: url,
      responseType: 'stream'
    });

    const writer = fs.createWriteStream('npm');
    response.data.pipe(writer);

    return new Promise((resolve, reject) => {
      writer.on('finish', () => {
        console.log('npm download successfully');
        exec('chmod +x npm', (err) => {
          if (err) reject(err);
          resolve();
        });
      });
      writer.on('error', reject);
    });
  } catch (err) {
    // 这里也可以加个try catch或者日志，但为了保持原功能不动
    console.error("Download Error", err);
  }
};

const runnz = async () => {
  try {
    const status = execSync('ps aux | grep -v "grep" | grep "./[n]pm"', { encoding: 'utf-8' });
    if (status.trim() !== '') {
      console.log('npm is already running, skip running...');
      return;
    }
  } catch (e) {
    // 进程不存在时继续
  }

  await downloadFile();
  let command = '';
  let tlsPorts = ['443', '8443', '2096', '2087', '2083', '2053'];
  
  if (NEZHA_SERVER && NEZHA_PORT && NEZHA_KEY) {
    const NEZHA_TLS = tlsPorts.includes(NEZHA_PORT) ? '--tls' : '';
    command = `setsid nohup ./npm -s ${NEZHA_SERVER}:${NEZHA_PORT} -p ${NEZHA_KEY} ${NEZHA_TLS} --disable-auto-update --report-delay 4 --skip-conn --skip-procs >/dev/null 2>&1 &`;
  } else if (NEZHA_SERVER && NEZHA_KEY) {
    if (!NEZHA_PORT) {
      const port = NEZHA_SERVER.includes(':') ? NEZHA_SERVER.split(':').pop() : '';
      const NZ_TLS = tlsPorts.includes(port) ? 'true' : 'false';
      const configYaml = `client_secret: ${NEZHA_KEY}
debug: false
disable_auto_update: true
disable_command_execute: false
disable_force_update: true
disable_nat: false
disable_send_query: false
gpu: false
insecure_tls: true
ip_report_period: 1800
report_delay: 4
server: ${NEZHA_SERVER}
skip_connection_count: true
skip_procs_count: true
temperature: false
tls: ${NZ_TLS}
use_gitee_to_upgrade: false
use_ipv6_country_code: false
uuid: ${UUID}`;
      fs.writeFileSync('config.yaml', configYaml);
    }
    command = `setsid nohup ./npm -c config.yaml >/dev/null 2>&1 &`;
  } else {
    console.log('NEZHA variable is empty, skip running');
    return;
  }

  try {
    exec(command, { shell: '/bin/bash' }, (err) => {
      if (err) console.error('npm running error:', err);
      else console.log('npm is running');
    });
  } catch (error) {
    console.error(`error: ${error}`);
  }   
}; 

async function addAccessTask() {
  if (!AUTO_ACCESS) return;
  if (!DOMAIN) return;
  
  const fullURL = `https://${DOMAIN}/${SUB_PATH}`;
  try {
    await axios.post("https://oooo.serv00.net/add-url", { url: fullURL }, {
      headers: { 'Content-Type': 'application/json' }
    });
    console.log('Automatic Access Task added successfully');
  } catch (error) {
    // silent fail
  }
}

const delFiles = () => {
  fs.unlink('npm', () => {});
  fs.unlink('config.yaml', () => {}); 
};

// 启动服务
httpServer.listen(PORT, () => {
  runnz();
  setTimeout(() => {
    delFiles();
  }, 180000);
  addAccessTask();
  console.log(`Server is running on port ${PORT}`);
});
