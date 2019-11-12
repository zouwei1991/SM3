using System;
using System.Text;

namespace Encryption
{
    public class SM3
    {
        private const uint T1 = 0x79cc4519;

        private const uint T2 = 0x7a879d8a;

        /// <summary>
        /// sm3加密
        /// </summary>
        /// <param name="message">输入数组</param>
        /// <returns></returns>
        public byte[] Compute(byte[] message)
        {
            if (message == null)
                throw new ArgumentNullException();
            if (message.Length > Math.Pow(2, 61))
                throw new Exception("输入长度超出范围,最大长度不应超过2^31个字节");
            V origin = new V();
            byte[] fillMessage = FillMessage(message);
            int n = fillMessage.Length / 64;
            for (int i = 0; i < n; i++)
            {
                byte[] groupBytes = new byte[64];
                for (int j = 0; j < groupBytes.Length; j++)
                {
                    groupBytes[j] = fillMessage[64 * i + j];
                }
                uint[] splitArray = SplitMessage(groupBytes);
                origin = CF(origin, splitArray);
            }
            return origin.ToBytes();
        }

        /// <summary>
        /// sm3算法发回哈希值
        /// </summary>
        /// <param name="message"></param>
        /// <returns></returns>
        public string GetComputeCode(byte[] message)
        {
            if (message == null)
                throw new ArgumentNullException();
            if (message.Length > Math.Pow(2, 61))
                throw new Exception("输入长度超出范围,最大长度不应超过2^31个字节");
            V origin = new V();
            byte[] fillMessage = FillMessage(message);
            int n = fillMessage.Length / 64;
            for (int i = 0; i < n; i++)
            {
                byte[] groupBytes = new byte[64];
                for (int j = 0; j < groupBytes.Length; j++)
                {
                    groupBytes[j] = fillMessage[64 * i + j];
                }
                uint[] splitArray = SplitMessage(groupBytes);
                origin = CF(origin, splitArray);
            }
            return origin.ToHashCode();
        }

        /// <summary>
        /// 根据输入字符数组获取填充后的数组
        /// </summary>
        /// <param name="message"></param>
        /// <returns></returns>
        private byte[] FillMessage(byte[] message)
        {
            ulong length = (ulong)message.Length * 8;
            int n = ((int)length + 65) / 512 + 1;
            int k = 512 * n - (int)length - 65;
            int fillLength = (1 + k) / 8;
            byte[] fillBytes = new byte[fillLength];
            for (int i = 0; i < fillLength; i++)
            {
                if (i == 0)
                {
                    fillBytes[i] = (byte)1 << 7;
                }
                else
                {
                    fillBytes[i] = (byte)0;
                }
            }
            byte[] tailBytes = new byte[8];
            ulong mask = 255;
            for (int i = 0; i < tailBytes.Length; i++)
            {
                byte b = (byte)((length & mask << (tailBytes.Length - i - 1) * 8) >> (tailBytes.Length - i - 1) * 8);
                tailBytes[i] = b;
            }
            byte[] result = new byte[message.Length + fillLength + 8];
            for (int i = 0; i < result.Length; i++)
            {
                if (i < message.Length)
                {
                    result[i] = message[i];
                }
                else if (i >= message.Length && i < message.Length + fillLength)
                {
                    result[i] = fillBytes[i - message.Length];
                }
                else
                {
                    result[i] = tailBytes[i - message.Length - fillLength];
                }
            }
            return result;
        }

        /// <summary>
        /// 获取扩展后的数组
        /// </summary>
        /// <param name="groupMessage"></param>
        /// <returns></returns>
        private uint[] SplitMessage(byte[] groupMessage)
        {
            uint[] splitArray = new uint[132];
            for (int i = 0; i < 16; i++)
            {
                byte[] b = new byte[4];
                for (int j = 0; j < b.Length; j++)
                {
                    b[j] = groupMessage[4 * i + j];
                }
                uint s = Getuint(b);
                splitArray[i] = s;
            }
            for (int j = 16; j <= 67; j++)
            {
                uint s = (uint)(splitArray[j - 16] ^ splitArray[j - 9] ^ CircleLeft(splitArray[j - 3], 15));
                uint r = (uint)(P1(s) ^ CircleLeft(splitArray[j - 13], 7) ^ splitArray[j - 6]);
                splitArray[j] = r;
            }
            for (int j = 0; j <= 63; j++)
            {
                uint s = (uint)(splitArray[j] ^ splitArray[j + 4]);
                splitArray[j + 68] = s;
            }

            return splitArray;
        }

        /// <summary>
        /// 压缩函数
        /// </summary>
        /// <param name="origin"></param>
        /// <param name="SplitArray"></param>
        /// <returns></returns>
        private V CF(V origin, uint[] SplitArray)
        {
            V copy = origin.Clone();
            uint SS1, SS2, TT1, TT2;
            for (int i = 0; i <= 63; i++)
            {
                SS1 = CircleLeft(ModPlus(ModPlus(CircleLeft(origin.A, 12), origin.E), CircleLeft(Tj(i), (i % 32))), 7);
                SS2 = SS1 ^ CircleLeft(origin.A, 12);
                TT1 = ModPlus(ModPlus(ModPlus(FFj(origin.A, origin.B, origin.C, i), origin.D), SS2), SplitArray[i + 68]);
                TT2 = ModPlus(ModPlus(ModPlus(GGj(origin.E, origin.F, origin.G, i), origin.H), SS1), SplitArray[i]);
                origin.D = origin.C;
                origin.C = CircleLeft(origin.B, 9);
                origin.B = origin.A;
                origin.A = TT1;
                origin.H = origin.G;
                origin.G = CircleLeft(origin.F, 19);
                origin.F = origin.E;
                origin.E = P0(TT2);
            }
            origin.A = origin.A ^ copy.A;
            origin.B = origin.B ^ copy.B;
            origin.C = origin.C ^ copy.C;
            origin.D = origin.D ^ copy.D;
            origin.E = origin.E ^ copy.E;
            origin.F = origin.F ^ copy.F;
            origin.G = origin.G ^ copy.G;
            origin.H = origin.H ^ copy.H;
            return origin;
        }

        #region 置换函数

        private uint P0(uint input)
        {
            return (uint)(input ^ CircleLeft(input, 9) ^ CircleLeft(input, 17));
        }

        private uint P1(uint input)
        {
            return (uint)(input ^ CircleLeft(input, 15) ^ CircleLeft(input, 23));
        }

        #endregion       
       
        #region 布尔函数

        private uint FFj(uint X, uint Y, uint Z, int j)
        {
            uint result = 0;
            if (j >= 0 && j <= 15)
            {
                result = X ^ Y ^ Z;
            }
            if (j >= 16 && j <= 63)
            {
                result = (X & Y) | (X & Z) | (Y & Z);
            }
            return result;
        }

        private uint GGj(uint X, uint Y, uint Z, int j)
        {
            uint result = 0;
            if (j >= 0 && j <= 15)
            {
                result = X ^ Y ^ Z;
            }
            if (j >= 16 && j <= 63)
            {
                result = (X & Y) | (~X & Z);
            }
            return result;
        }

        #endregion

        /// <summary>
        /// 获取常量
        /// </summary>
        /// <param name="j"></param>
        /// <returns></returns>
        private uint Tj(int j)
        {
            if (j >= 0 && j <= 15)
            {
                return T1;
            }
            if (j >= 16 && j <= 63)
            {
                return T2;
            }
            return 0;
        }

        /// <summary>
        /// 模加
        /// </summary>
        /// <param name="X"></param>
        /// <param name="Y"></param>
        /// <returns></returns>
        private uint ModPlus(uint X, uint Y)
        {
            ulong mod = (ulong)Math.Pow(2, 32);
            uint result = (uint)((X + Y) % mod);
            return result;
        }

        /// <summary>
        /// 循环左移
        /// </summary>
        /// <param name="input"></param>
        /// <param name="bit"></param>
        /// <returns></returns>
        private uint CircleLeft(uint input, int bit)
        {
            return (input >> (32 - bit) | input << bit);
        }

        private uint Getuint(byte[] bytes)
        {
            uint s = 0;
            for (int i = 0; i < bytes.Length; i++)
            {
                uint mask = bytes[i];
                s = (uint)(s | mask << (bytes.Length - i - 1) * 8);
            }
            return s;
        }

        /// <summary>
        /// 压缩迭代值
        /// </summary>
        private class V
        {
            public uint A = 0x7380166F;

            public uint B = 0x4914B2B9;

            public uint C = 0x172442D7;

            public uint D = 0xDA8A0600;

            public uint E = 0xA96F30BC;

            public uint F = 0x163138AA;

            public uint G = 0xE38DEE4D;

            public uint H = 0xB0FB0E4E;

            public V Clone()
            {
                V n = new V();
                n.A = this.A;
                n.B = this.B;
                n.C = this.C;
                n.D = this.D;
                n.E = this.E;
                n.F = this.F;
                n.G = this.G;
                n.H = this.H;
                return n;
            }

            public byte[] ToBytes()
            {
                byte[] result = new byte[32];
                uint mask = 255;
                for (int i = 0; i < 32; i++)
                {
                    int n = i / 4 + 1;
                    int mod = i % 4;
                    byte b = 0;
                    switch (n)
                    {
                        case 1:
                            b = (byte)((A & mask << (4 - mod) * 8) >> (4 - mod) * 8);
                            break;
                        case 2:
                            b = (byte)((B & mask << (4 - mod) * 8) >> (4 - mod) * 8);
                            break;
                        case 3:
                            b = (byte)((C & mask << (4 - mod) * 8) >> (4 - mod) * 8);
                            break;
                        case 4:
                            b = (byte)((D & mask << (4 - mod) * 8) >> (4 - mod) * 8);
                            break;
                        case 5:
                            b = (byte)((E & mask << (4 - mod) * 8) >> (4 - mod) * 8);
                            break;
                        case 6:
                            b = (byte)((F & mask << (4 - mod) * 8) >> (4 - mod) * 8);
                            break;
                        case 7:
                            b = (byte)((G & mask << (4 - mod) * 8) >> (4 - mod) * 8);
                            break;
                        case 8:
                            b = (byte)((H & mask << (4 - mod) * 8) >> (4 - mod) * 8);
                            break;
                        default:
                            break;
                    }
                    result[i] = b;
                }
                return result;
            }

            public string ToHashCode()
            {
                StringBuilder sb = new StringBuilder();
                string temp = string.Empty;
                temp = Convert.ToString(A, 16);
                sb.Append(temp);
                temp = Convert.ToString(B, 16);
                sb.Append(temp);
                temp = Convert.ToString(C, 16);
                sb.Append(temp);
                temp= Convert.ToString(D, 16);
                sb.Append(temp);
                temp= Convert.ToString(E, 16);
                sb.Append(temp);
                temp = Convert.ToString(F, 16);
                sb.Append(temp);
                temp = Convert.ToString(G, 16);
                sb.Append(temp);
                temp = Convert.ToString(H, 16);
                sb.Append(temp);            
                return sb.ToString();
            }
        }

    }
}
