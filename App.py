import string
import numpy as np
from egcd import egcd
import math
import tkinter as tk
from tkinter import messagebox
from PIL import ImageTk, Image 
from Crypto.Cipher import DES
from Crypto.Util.Padding import pad, unpad
from Crypto.Random import get_random_bytes
#Omar Adlii Abd ElHalim
#190110
def bin2hex(s):
    mp = {"0000": '0',"0001": '1',"0010": '2',"0011": '3', "0100": '4',
          "0101": '5',"0110": '6',"0111": '7',"1000": '8',"1001": '9',
          "1010": 'A',"1011": 'B',"1100": 'C',"1101": 'D',"1110": 'E',"1111": 'F'}
    hex = ""
    for i in range(0, len(s), 4):
        ch = ""
        ch = ch + s[i]
        ch = ch + s[i + 1]
        ch = ch + s[i + 2]
        ch = ch + s[i + 3]
        hex = hex + mp[ch]
    return hex
def hex2bin(s):
    mp = {'0': "0000",'1': "0001",'2': "0010",'3': "0011",'4': "0100",'5': "0101",'6': "0110",
          '7': "0111",'8': "1000",'9': "1001",'A': "1010",'B': "1011",'C': "1100",'D': "1101",'E': "1110",'F': "1111"}
    bin = ""
    for i in range(len(s)):
        bin = bin + mp[s[i]]
    return bin
#Omar Adlii Abd ElHalim
#190110
class encryption:
    def __init__(self):
        self.alph='abcdefghijklmnopqrstuvwxyz'
        self.alph1='abcdefghiklmnopqrstuvwxyz'
    def clean(self,Str):
        self.Str=Str.lower()
        self.Str=self.Str.replace(" ", "")
        self.Str=self.Str.translate(str.maketrans('', '', string.punctuation))
        return self.Str
        
    def shift_cipher(self,e,m):
        self.m=self.clean(m)
        self.e=e
        self.encrp=[]
        for i in self.m:
            self.encrp.append(self.alph[(self.alph.index(i)+self.e)%26])

        return ''.join(self.encrp)
    def Monoalphabetic(self,k,m):
        self.m=self.clean(m)
        self.k=self.clean(k)
        self.newDic=''.join(sorted(set(self.k+self.alph), key=(self.k+self.alph).index))
        self.encrp=[]
        for i in self.m:
            self.encrp.append(self.newDic[self.alph.index(i)])
        return ''.join(self.encrp)
    def AffineCipher(self,k,m):
        self.m=self.clean(m)
        self.k=k
        self.encrp=[]
        for i in self.m:
            self.encrp.append(self.alph[(self.alph.index(i)*self.k[0]+self.k[1])%26])

        return ''.join(self.encrp)
    def playfair(self,k,m):
        self.m=self.clean(m)
        self.m=self.m.replace("j", "i")
        for i in range(1,len(self.m),2):
            if self.m[i]==self.m[i-1]:
                self.m=self.m[:i]+'x'+self.m[i:]
        if len(self.m)%2:
            self.m=self.m+'z'  
        self.k=self.clean(k)
        self.newDic=''.join(sorted(set(self.k+self.alph1), key=(self.k+self.alph1).index))
        self.ind=[self.newDic.index(i)for i in self.m]
        self.e=[]
        for i in range(0,len(self.ind),2):
            #CHECK COLUMNS 
            if self.ind[i]%5 == self.ind[i+1]%5:
                if self.ind[i]>=20:
                    self.e.append(self.ind[i]-20)
                else:
                    self.e.append(self.ind[i]+5)
                if self.ind[i+1]>=20:
                    self.e.append(self.ind[i+1]-20)
                else:
                    self.e.append(self.ind[i+1]+5)
            #CHECK ROWS
            elif int(self.ind[i]/5) == int(self.ind[i+1]/5):
                if self.ind[i] in (4,9,14,19,24):
                    self.e.append(self.ind[i]-4)
                    self.e.append(self.ind[i+1]+1)
                elif self.ind[i+1] in (4,9,14,19,24):
                    self.e.append(self.ind[i]+1)
                    self.e.append(self.ind[i+1]-4)
                else:
                    self.e.append(self.ind[i]+1)
                    self.e.append(self.ind[i+1]+1)
            else:
                x=abs(self.ind[i]%5-self.ind[i+1]%5)
                if self.ind[i]%5 < self.ind[i+1]%5:
                    self.e.append(self.ind[i]+x)
                    self.e.append(self.ind[i+1]-x)
                else:
                    self.e.append(self.ind[i]-x)
                    self.e.append(self.ind[i+1]+x)        
        self.encrp =[self.newDic[i]for i in self.e]
        return ''.join(self.encrp)
    def vigenere_cipher(self,n,k,m):
        self.m=self.clean(m)
        self.k=self.clean(k)
        self.Kind=[self.alph.index(x) for x in self.k]
        self.ind=[self.alph.index(x) for x in self.m]
        
        
        while(len(self.Kind)!=n):
            if len(self.Kind)>n:
                self.Kind.pop()
            else:
                self.Kind+=self.Kind
        
        while(len(self.Kind)!=len(self.ind)):
            if len(self.Kind)>len(self.ind):
                self.Kind.pop()
            else:
                self.Kind+=self.Kind
        self.encrp=(np.array(self.ind)+np.array(self.Kind))%26
        
        return ''.join([self.alph[i]for i in self.encrp])
    
    def Substitution_Cipher(self,m,k):
        self.m=self.clean(m)
        self.k=self.clean(k)
        self.encrp = ''
        count = 0
        for char in self.m:
            self.encrp += self.k[self.alph.index(char)]
            count = count+1
        return self.encrp
    def Hill_Cipher(self,m,k):
        if type(k)==type(np.array([])):
            KEY=k
        else:
            KEY=np.array([self.alph.index(i) for i in self.clean(k)])
            s=int(np.sqrt(len(KEY)))
            KEY=KEY.reshape(s,s)
        self.m=self.clean(m)
        messageMatrix=[self.alph.index(i) for i in self.m]
        s=KEY.shape[0]
        while(len(messageMatrix)%s):
            messageMatrix.append(25)
        encrptvector=[]
        for i in range(0,len(messageMatrix),s):
            x=np.array(messageMatrix[i:i+s])
            re=KEY@x%26
            encrptvector.append([i for i in re])
        self.encrp=''.join([self.alph[i]for i in np.array(encrptvector).flatten()])
        count = 0
        for char in self.m:
            count = count+1
              
        return self.encrp
    def Rail_Fence(self,m, k):
        c_text = [[] for _ in range(k)]
        rail = 0
        direction = 1
        self.m=self.clean(m)
        for char in self.m:
            c_text[rail].append(char)
            rail = rail + direction
            if rail == k - 1 or rail == 0:
                direction = direction * (-1)

        self.encrp = ''.join([''.join(rail) for rail in c_text])
        count = 0
        for char in self.m:
            count = count+1
        return self.encrp
    def Row_Transposition(self,m,k):
        self.m=m
        rows = int(math.ceil(len(self.m) / len(k)))
        self.m += '_' * (rows * len(k) - len(self.m))
        grid = [['' for _ in range(len(k))] for _ in range(rows)]
        index = 0
        for i in range(rows):
            for j in range(len(k)):
                grid[i][j] = self.m[index]
                index += 1
        sorted_columns = [x[0] for x in sorted(enumerate(k), key=lambda x: x[1])]
        self.encrp = ''
        for col in sorted_columns:
            for i in range(rows):
                self.encrp += grid[i][col]
        return self.encrp
    def des(self,m,k):
        if len(k)==64:
            k=bitstring_to_bytes(k)
        elif len(k)==16:
            k=hex2bin(k)
            k=bitstring_to_bytes(k)
        cipher = DES.new(k, DES.MODE_ECB)
        ciphertext = cipher.encrypt(pad(m.encode(), DES.block_size))
        return ciphertext.hex()
def bitstring_to_bytes(s):
    v = int(s, 2)
    b = bytearray()
    while v:
        b.append(v & 0xff)
        v >>= 8
    return bytes(b[::-1])
def modinv(a, m):
    gcd, x, y = egcd(a, m)
    if gcd != 1:
        return None  # modular inverse does not exist
    else:
        return x % m
#Omar Adlii Abd ElHalim
#190110
class decryption():
    def __init__(self):
        self.alph='abcdefghijklmnopqrstuvwxyz'
        self.alph1='abcdefghiklmnopqrstuvwxyz'
    def clean(self,Str):
        self.Str=Str.lower()
        self.Str=self.Str.replace(" ", "")
        self.Str=self.Str.translate(str.maketrans('', '', string.punctuation))
        return self.Str
    def shift_cipher(self,e,m):
        self.m=self.clean(m)
        self.e=e
        self.dencrp=[]
        for i in self.m:
            self.dencrp.append(self.alph[(self.alph.index(i)-self.e)%26])
        return ''.join(self.dencrp)
    def Monoalphabetic(self,k,m):
        self.m=self.clean(m)
        self.k=self.clean(k)
        self.newDic=''.join(sorted(set(self.k+self.alph), key=(self.k+self.alph).index))
        self.dencrp=[]
        for i in self.m:
            self.dencrp.append(self.alph[self.newDic.index(i)])
        return ''.join(self.dencrp)
    def AffineCipher(self,k,m):
        self.m=self.clean(m)
        self.k=(modinv(k[0],26),k[1])
        self.dencrp=[]
        for i in self.m:
            self.dencrp.append(self.alph[((self.alph.index(i)-self.k[1])*self.k[0])%26])
        
        return ''.join(self.dencrp)
    def playfair(self,k,m):
        self.m=self.clean(m)
        self.m=self.m.replace("j", "i")
        for i in range(1,len(self.m),2):
            if self.m[i]==self.m[i-1]:
                self.m=self.m[:i]+'x'+self.m[i:]
        if len(self.m)%2:
            self.m=self.m+'x'
        self.k=self.clean(k)
    
        self.newDic=''.join(sorted(set(self.k+self.alph1), key=(self.k+self.alph1).index))
       
        self.ind=[self.newDic.index(i)for i in self.m]
        self.d=[]
        for i in range(0,len(self.ind),2):
            
            #CHECK COLUMNS 
            if self.ind[i]%5 == self.ind[i+1]%5:
                if self.ind[i]<=4:
                    self.d.append(self.ind[i]+20)
                else:
                    self.d.append(self.ind[i]-5)
                if self.ind[i+1]<=4:
                    self.d.append(self.ind[i+1]+20)
                else:
                    self.d.append(self.ind[i+1]-5)
                
            #CHECK ROWS 
            elif int(self.ind[i]/5) == int(self.ind[i+1]/5):
                if self.ind[i] in (0,5,10,15,20):
                    self.d.append(self.ind[i]+4)
                    self.d.append(self.ind[i+1]-1)
                elif self.ind[i+1] in (0,5,10,15,20):
                    self.d.append(self.ind[i]-1)
                    self.d.append(self.ind[i+1]+4)
                else:
                    self.d.append(self.ind[i]-1)
                    self.d.append(self.ind[i+1]-1)
            else:
                x=abs(self.ind[i]%5-self.ind[i+1]%5)
                if self.ind[i]%5 < self.ind[i+1]%5:
                    self.d.append(self.ind[i]+x)
                    self.d.append(self.ind[i+1]-x)
                else:
                    self.d.append(self.ind[i]-x)
                    self.d.append(self.ind[i+1]+x)
                    
        self.dencrp =[self.newDic[i]for i in self.d]
        count = 0
        
        return ''.join(self.dencrp)
    def vigenere_cipher(self,n,k,m):
        self.m=self.clean(m)
        self.k=self.clean(k)
        self.Kind=[self.alph.index(x) for x in self.k]
        self.ind=[self.alph.index(x) for x in self.m]
        while(len(self.Kind)!=n):
            if len(self.Kind)>n:
                self.Kind.pop()
            else:
                self.Kind+=self.Kind
        
        while(len(self.Kind)!=len(self.ind)):
            if len(self.Kind)>len(self.ind):
                self.Kind.pop()
            else:
                self.Kind+=self.Kind
       
        self.dencrp=(np.array(self.ind)-np.array(self.Kind))%26
        
        return ''.join([self.alph[i]for i in self.dencrp])
    def Substitution_Cipher(self,m,k):
        self.m=self.clean(m)
        self.k=self.clean(k)
       
        self.dencrp = ''
        count = 0
        for char in self.m:
            self.dencrp += self.alph[self.k.index(char)]
            count = count+1
            
        return self.dencrp
    def Hill_Cipher(self,m,k):
        if type(k)==type(np.array([])):
            KEY=k
        else:
            KEY=np.array([self.alph.index(i) for i in self.clean(k)])
            s=int(np.sqrt(len(KEY)))
            KEY=KEY.reshape(s,s)
        self.m=self.clean(m)
        messageMatrix=[self.alph.index(i) for i in self.m]
        s=KEY.shape[0]
        while(len(messageMatrix)%s):
            messageMatrix.append(25)
       
        det = int(np.round(np.linalg.det(KEY)))
        det_inv = egcd(det, 26)[1] % 26  
        KEY_matrix_modulus_inv = (det_inv * np.round(det * np.linalg.inv(KEY)).astype(int) % 26)
        dencrptvector=[]
        for i in range(0,len(messageMatrix),s):
            x=np.array(messageMatrix[i:i+s])
            re=KEY_matrix_modulus_inv@x%26
            dencrptvector.append([i for i in re])
            
        self.dencrp=''.join([self.alph[i]for i in np.array(dencrptvector).flatten()])
       
        return self.dencrp
    def Rail_Fence(self,m, k):
        rail = [['\n' for i in range(len(m))]for j in range(k)]
        dir_down = None
        row, col = 0, 0
        
        for i in range(len(m)):
            if row == 0:
                dir_down = True
            if row == k - 1:
                dir_down = False

            rail[row][col] = '*'
            col += 1
            if dir_down:
                row += 1
            else:
                row -= 1

        index = 0
        for i in range(k):
            for j in range(len(m)):
                if ((rail[i][j] == '*') and (index < len(m))):
                    rail[i][j] = m[index]
                    index += 1

        result = []
        row, col = 0, 0
        for i in range(len(m)):
            if row == 0:
                dir_down = True
            if row == k-1:
                dir_down = False

            if (rail[row][col] != '*'):
                result.append(rail[row][col])
                col += 1

            if dir_down:
                row += 1
            else:
                row -= 1
        self.dencrp=("".join(result))
         
        return self.dencrp
    def Row_Transposition(self,m,k):
        ciphertext=m
        key=k
        rows = int(math.ceil(len(ciphertext) / len(key)))
       
        ciphertext += '_' * (rows * len(key) - len(ciphertext))
        sorted_columns = [x[0] for x in sorted(enumerate(key), key=lambda x: x[1])]
        grid = [['' for _ in range(len(key))] for _ in range(rows)]
        index = 0
        for col in sorted_columns:
            for i in range(rows):
                grid[i][col] = ciphertext[index]
                index += 1
        plaintext = ''
        for i in range(rows):
            for j in range(len(key)):
                plaintext += grid[i][j]
       
        return plaintext.replace('_', '')
    def des(self,m,k):
        if len(k)==64:
            k=bitstring_to_bytes(k)
        elif len(k)==16:
            k=hex2bin(k)
            k=bitstring_to_bytes(k)
        cipher = DES.new(k, DES.MODE_ECB)
        decrypted = cipher.decrypt(bytes.fromhex(m))
        plaintext = unpad(decrypted, DES.block_size).decode()
        return plaintext
    
def encrypt_message():
    algorithm = algorithm_choice.get()
    message = message_entry.get()
    key = key_entry.get()
    e=encryption()
    try:
        if not message or not key:
            messagebox.showwarning("Warning", "Please enter both message and key.")
            return

        encrypted_message = ""
        if algorithm == "Caesar Cipher":
            key = int(key)
            encrypted_message = e.shift_cipher(key,message)
        elif algorithm == "Monoalphabetic":
            encrypted_message = e.Monoalphabetic(key,message)
        elif algorithm == "Affine Cipher":
            key=key.replace('(','')
            key=key.replace(')','')
            int(key.split(',')[0])
            encrypted_message = e.AffineCipher((int(key.split(',')[0]),int(key.split(',')[1])),message)
        elif algorithm == "Playfair Cipher":
            encrypted_message = e.playfair(key,message)
        elif algorithm == "Vigenere Cipher":
            key=int(key)
            encrypted_message = e.vigenere_cipher(key,message)
        elif algorithm == "Substitution Cipher":
            encrypted_message = e.Substitution_Cipher(message,key)
        elif algorithm == "Hill Cipher":
            key=key.replace('[','')
            key=key.replace(']','')
            if key.count(',')==8:
                key=np.array([[int(key.split(',')[0]),int(key.split(',')[1]),int(key.split(',')[2])],
                          [int(key.split(',')[3]),int(key.split(',')[4]),int(key.split(',')[5])],
                          [int(key.split(',')[6]),int(key.split(',')[7]),int(key.split(',')[8])]])
            elif key.count(',')==3:
                key=np.array([[int(key.split(',')[0]),int(key.split(',')[1])],
                              [int(key.split(',')[2]),int(key.split(',')[3])]])
            encrypted_message = e.Hill_Cipher(message,key)
        elif algorithm == "Rail Fence Cipher":
            encrypted_message = e.Rail_Fence(message, int(key))
        elif algorithm == "Row Transposition":
            encrypted_message =e.Row_Transposition(message, key)
        elif algorithm == "DES":
            encrypted_message = e.des(message, key)
    except Exception as e:
        messagebox.showwarning("Warning",str(e))
        return

    encrypted_entry.delete(0, tk.END)
    encrypted_entry.insert(tk.END, encrypted_message)


def decrypt_message():
    algorithm = algorithm_choice.get()
    encrypted_message = encrypted_entry.get()
    key = key_entry.get()
    d=decryption()
    try:
        if not encrypted_message or not key:
            messagebox.showwarning("Warning", "Please enter both message and key.")
            return

        decrypted_message = ""
        if algorithm == "Caesar Cipher":
            key = int(key)
            decrypted_message = d.shift_cipher(key,encrypted_message)
        elif algorithm == "Monoalphabetic":
            decrypted_message = d.Monoalphabetic(key,encrypted_message)
        elif algorithm == "Affine Cipher":
            key=key.replace('(','')
            key=key.replace(')','')
            int(key.split(',')[0])
            decrypted_message = d.AffineCipher((int(key.split(',')[0]),int(key.split(',')[1])),encrypted_message)
        elif algorithm == "Playfair Cipher":
            decrypted_message = d.playfair(key,encrypted_message)
        elif algorithm == "Vigenere Cipher":
            key=int(key)
            decrypted_message = d.vigenere_cipher(key,encrypted_message)
        elif algorithm == "Substitution Cipher":
            decrypted_message = d.Substitution_Cipher(encrypted_message,key)
        elif algorithm == "Hill Cipher":
            key=key.replace('[','')
            key=key.replace(']','')
            if key.count(',')==8:
                key=np.array([[int(key.split(',')[0]),int(key.split(',')[1]),int(key.split(',')[2])],
                          [int(key.split(',')[3]),int(key.split(',')[4]),int(key.split(',')[5])],
                          [int(key.split(',')[6]),int(key.split(',')[7]),int(key.split(',')[8])]])
            elif key.count(',')==3:
                key=np.array([[int(key.split(',')[0]),int(key.split(',')[1])],
                              [int(key.split(',')[2]),int(key.split(',')[3])]])
            decrypted_message = d.Hill_Cipher(encrypted_message,key)
        elif algorithm == "Rail Fence Cipher":
            decrypted_message = d.Rail_Fence(encrypted_message, int(key))
        elif algorithm == "Row Transposition":
            decrypted_message =d.Row_Transposition(encrypted_message, key)
        elif algorithm == "DES":
            decrypted_message = d.des(encrypted_message, key)
    except Exception as e:
        messagebox.showwarning("Warning",str(e))
        return
    decrypted_entry.delete(0, tk.END)
    decrypted_entry.insert(tk.END, decrypted_message)


# Create the main window
window = tk.Tk()
window.geometry("500x500")
img= tk.PhotoImage(file='background.png', master= window)
img_label= tk.Label(window,image=img)

#define the position of the image
img_label.place(x=0, y=0)
window.title("Encryption & Decryption")

# Create the algorithm choice dropdown
algorithm_label = tk.Label(window, text="Algorithms:", font=('Times', 18),bg='#223922',fg='#EFF3A2')
algorithm_label.place(x=50,y=30)
#algorithm_label.pack()

algorithm_choice = tk.StringVar()
algorithm_choice.set("Caesar Cipher")

algorithm_dropdown = tk.OptionMenu(window, algorithm_choice,"Caesar Cipher","Monoalphabetic",
                                   "Affine Cipher","Playfair Cipher","Vigenere Cipher","Substitution Cipher",
                                  "Hill Cipher","Rail Fence Cipher","Row Transposition","DES")
algorithm_dropdown.config(width=15,height=1,bg='#EFF3A2')
algorithm_dropdown.place(x=200,y=30)

# Create the message entry
message_label = tk.Label(window, text="Plaintext:",font=('Times', 18),bg='#223922',fg='#EFF3A2')
message_label.place(x=50,y=75)

message_entry = tk.Entry(window,font=('Times', 18),bg='#EFF3A2')
message_entry.place(x=200,y=75)

# Create the key entry
key_label = tk.Label(window, text="Key:",font=('Times', 18),bg='#223922',fg='#EFF3A2')
key_label.place(x=50,y=120)

key_entry = tk.Entry(window,font=('Times', 18),bg='#EFF3A2')
key_entry.place(x=200,y=120)

# Create the encrypt button
encrypt_button = tk.Button(window, text="Encrypt", command=encrypt_message,font=('Times', 18),bg='#223922',fg='#EFF3A2')
encrypt_button.config(width=25,height=1)
encrypt_button.place(x=80,y=180)

# Create the encrypted message entry
encrypted_label = tk.Label(window, text="Ciphertext:",font=('Times', 18),bg='#223922',fg='#EFF3A2')
encrypted_label.place(x=50,y=260)

encrypted_entry = tk.Entry(window,font=('Times', 18),bg='#EFF3A2')
encrypted_entry.place(x=200,y=260)

# Create the decrypt button
decrypt_button = tk.Button(window, text="Decrypt", command=decrypt_message,font=('Times', 18),bg='#223922',fg='#EFF3A2')
decrypt_button.config(width=25,height=1)
decrypt_button.place(x=80,y=315)

# Create the decrypted message entry
decrypted_label = tk.Label(window, text="Message:",font=('Times', 18),bg='#223922',fg='#EFF3A2')
decrypted_label.place(x=50,y=390)

decrypted_entry = tk.Entry(window,font=('Times', 18),bg='#EFF3A2')
decrypted_entry.place(x=200,y=390)
# Run the main window loop
window.mainloop()

